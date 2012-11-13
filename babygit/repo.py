# Copyright 2012 Google Inc.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Utilities for manipulating a repo. This layers on top of a store to provide
# raw object storage

import binascii
import logging

import babygit

class Repo:
    def __init__(self, store):
        self.store = store
    def gethead(self, head = 'refs/heads/master'):
        inforefs = self.store.getinforefs()
        return inforefs[head]  # todo: handle abbreviations, do search path
    def getroot(self, commitsha = None):
        if commitsha is None:
            commitsha = self.gethead()
        obj = self.store.getobj(commitsha)
        if babygit.obj_type(obj) != 'commit':
            raise ValueError('expected commit obj type')
        commitlines = obj[obj.find('\x00') + 1:].split('\n')
        for l in commitlines:
            if l.startswith('tree'):
                return l.split(' ')[1]
    def parse_tree(self, obj):
        if babygit.obj_type(obj) != 'tree': raise ValueError('wrong obj type')
        ix = obj.find('\x00') + 1
        if ix == 0: raise ValueError('missing nul')
        result = []
        while ix < len(obj):
            nul_ix = obj.find('\x00', ix)
            mode_and_name = obj[ix:nul_ix]
            mode, name = mode_and_name.split(' ', 1)
            sha = binascii.hexlify(obj[nul_ix + 1:nul_ix + 21])
            result.append((mode, name, sha))
            ix = nul_ix + 21
        return result
    def find_in_tree(self, parsed_tree, name):
        # Should be binary search
        for mode, n, sha in parsed_tree:
            if n == name:
                return mode, sha

    # Note: this mutates the parsed tree in place
    def set_in_tree(self, parsed_tree, mode, name, sha):
        for i in range(len(parsed_tree)):
            m, n, s = parsed_tree[i]
            if n == name:
                parsed_tree[i] = (mode, name, sha)
                return
            elif n > name:
                parsed_tree.insert(i, (mode, name, sha))
                return
        parsed_tree.append((mode, name, sha))

    def parse_commit(self, obj):
        result = {}
        result['parents'] = []
        if babygit.obj_type(obj) != 'commit': raise ValueError('wrong obj type')
        lines = babygit.obj_contents(obj).split('\n')
        for i, l in enumerate(lines):
            if l.startswith('tree '):
                result['tree'] = l.split(' ')[1]
            elif l.startswith('parent '):
                result['parents'].append(l.split(' ')[1])
            elif l.startswith('author '):
                result['author'] = l.split(' ', 1)[1]
            elif l.startswith('committer '):
                result['committer'] = l.split(' ', 1)[1]
            elif l == '':
                result['msg'] = '\n'.join(lines[i+1:])
                break
        return result

    # Get an object (tree or blob) corresponding to a path. Returns the obj
    # (ie string with type and length prepended in git style)
    def traverse(self, path, root = None):
        if root is None:
            root = self.getroot()
        splitpath = path.split('/')
        if splitpath[-1] == '': splitpath.pop()
        sha = root
        obj = self.store.getobj(sha)
        for i in range(len(splitpath)):
            if babygit.obj_type(obj) != 'tree':
                raise ValueError('expected tree')
            ptree = self.parse_tree(obj)
            mode_sha = self.find_in_tree(ptree, splitpath[i])
            if mode_sha is None:
                return None
            obj = self.store.getobj(mode_sha[1])
            t = babygit.obj_type(obj)
        return obj

    # just proxy these through so clients don't have to deal with the low-level
    # store directly
    def getobj(self, sha, verify = False):
        return self.store.getobj(sha, verify)

    # Return a set of (sha, data) tuples from walking the graph. Note that
    # this would be place to optimize getting the zlib-compressed data, to
    # avoid having to recompress, but that's for future.
    def walk(self, wants, haves):
        result = []
        done = set()
        queue = set(wants)
        while queue:
            sha = queue.pop()
            if sha in done or sha in haves:
                continue
            obj = self.store.getobj(sha)
            if obj is None:
                logging.debug('walk, can\'t find ' + `sha`)
                break
            result.append((sha, obj))
            done.add(sha)
            t = babygit.obj_type(obj)
            if t == 'commit':
                for l in babygit.obj_contents(obj).split('\n'):
                    if l == '':
                        break
                    elif l.startswith('tree ') or l.startswith('parent '):
                        queue.add(l.rstrip('\n').split(' ')[1])
            elif t == 'tree':
                for mode, name, sha in self.parse_tree(obj):
                    queue.add(sha)
        return result

    # return value is a list of tuples (path, change), where change is one of
    # 'add', 'delete', 'change'. May be extended to finer grained diffing later.
    # Arguments are tree object names. (Use getroot to resolve commits)
    def diff_tree(self, tree1, tree2):
        result = []
        self.diff_tree_recurse(tree1, tree2, result, '')
        return result

    def diff_tree_recurse(self, tree1, tree2, result, prefix):
        treeobj1 = self.store.getobj(tree1)
        if treeobj1 is None:
            logging.debug('missing tree1 ' + tree1)
            return
        ptree1 = self.parse_tree(treeobj1)
        treeobj2 = self.store.getobj(tree2)
        if treeobj2 is None:
            logging.debug('missing tree2 ' + tree2)
            return
        ptree2 = self.parse_tree(treeobj2)
        i = 0
        j = 0
        while i < len(ptree1) or j < len(ptree2):
            if j == len(ptree2) or (i < len(ptree1) and ptree1[i][1] < ptree2[j][1]):
                self.obj_enumerate(ptree1[i], result, prefix, 'delete')
                i += 1
            elif i == len(ptree1) or ptree1[i][1] > ptree2[j][1]:
                self.obj_enumerate(ptree2[j], result, prefix, 'add')
                j += 1
            else:
                name = ptree1[i][1]
                if ptree1[i][0] == '40000' and ptree2[j][0] == '40000':
                    if ptree1[i][2] != ptree2[j][2]:
                        self.diff_tree_recurse(ptree1[i][2], ptree2[j][2], result, prefix + name + '/')
                else:
                    if ptree1[i][2] != ptree2[j][2]:
                        result.append((prefix + name, 'change'))
                # ignore corner cases where it's a blob in one tree and a dir in another
                i += 1
                j += 1

    def obj_enumerate(self, mode_name_sha, result, prefix, change):
        mode, name, sha = mode_name_sha
        if mode == '40000':
            treeobj = self.store.getobj(sha)
            if treeobj is None:
                return
            for m_n_s in self.parse_tree(treeobj):
                self.obj_enumerate(m_n_s, result, prefix + name + '/', change)
        else:
            result.append((prefix + name, change))
