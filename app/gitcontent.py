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

# Low-level access to the git repository and content

import ghmarkup

import babygit.appengine
import babygit.babygit
import babygit.repo

s = babygit.appengine.AEStore()
r = babygit.repo.Repo(s)
babygit.babygit.ensure_repo(s)

def get_repo():
    return r

def traverse(gitpath):
    return r.traverse(gitpath)

def wiki_to_git_path(wiki_path):
    while wiki_path.startswith('/'):
        wiki_path = wiki_path[1:]
    return 'wiki/' + wiki_path + '.ghm'

# Here so that other pages can include bits of wiki content
def get_wiki_html(wikipath, basepath = '/'):
    obj = traverse(wiki_to_git_path(wikipath))
    if obj is None:
        return obj
    else:
        contents = babygit.babygit.obj_contents(obj)
        return ghmarkup.process_ghmarkup(contents, basepath)
