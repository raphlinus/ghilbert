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
        if babygit.obj_type(obj) != 'tree': raise ValueError('wrong blob type')
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

