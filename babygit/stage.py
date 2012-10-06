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

# Operations for reading and writing trees, most useful as a stage (which
# can then be committed). However, we're not going to do it as a big index
# file like git, it's just going to be a tree like any other.

import babygit
import logging
import time

def pack_tree(parsed_tree):
    raw = []
    for mode, name, sha in parsed_tree:
        raw.append(mode + ' ' + name + '\x00' + babygit.from_hex(sha))
    return ''.join(raw)

def checkout(repo, head = 'refs/heads/master'):
    headcommit = repo.gethead(head)
    tree = repo.getroot(headcommit)
    now = time.time()
    stagedict = {'parent': headcommit, 'tree': tree, 'date': now}
    repo.store.putstage(stagedict)

def getroot(repo):
    return repo.store.getstage()['tree']

# Replace (or add) the file at the path with the new contents. The return
# value is the new tree sha. Stores the blob, and any intermediate tree
# nodes, in the repo.
def save(repo, path, contents, root = None):
    splitpath = path.split('/')
    if splitpath[-1] == '': raise ValueError('can\'t save a blob in a dir')

    if root is None:
        root = repo.getroot()
    parsed_trees = []
    sha = root
    for i in range(len(splitpath)):
        if sha:
            obj = repo.getobj(sha)
        else:
            obj = None
        if obj is None:
            parsed_tree = []
        else:
            parsed_tree = repo.parse_tree(obj)
        parsed_trees.append(parsed_tree)
        if i < len(splitpath) - 1:
            mode_sha = repo.find_in_tree(parsed_tree, splitpath[i])
            if mode_sha is not None:
                sha = mode_sha[1]
            else:
                sha = None
    store = repo.store
    savesha = store.put('blob', contents)
    mode = '100644'
    for i in range(len(splitpath) - 1, -1, -1):
        repo.set_in_tree(parsed_trees[i], mode, splitpath[i], savesha)
        pack = pack_tree(parsed_trees[i])
        savesha = store.put('tree', pack)
        mode = '40000'
    return savesha

def add(repo, tree):
    stagedict = repo.store.getstage()
    stagedict['tree'] = tree
    stagedict['date'] = time.time()
    repo.store.putstage(stagedict)

def commit(repo, author, msg):
    stagedict = repo.store.getstage()
    commitobj = []
    commitobj.append('tree ' + stagedict['tree'] + '\n')
    commitobj.append('parent ' + stagedict['parent'] + '\n')
    commitobj.append('author ' +  author + ' ' + str(int(stagedict['date'])) + ' -0700\n')
    commitobj.append('committer ' + author + ' ' + str(int(time.time())) + ' -0700\n')
    commitobj.append('\n')
    commitobj.append(msg)
    logging.debug(''.join(commitobj))
    commitsha = repo.store.put('commit', ''.join(commitobj))
    logging.debug(commitsha)
    repo.store.setinforefs({'refs/heads/master': commitsha})
    return commitsha
