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

# Utilities for reading proof files from the git repo

import os.path
import StringIO
import logging

import babygit.appengine
import babygit.babygit
import babygit.repo

s = babygit.appengine.AEStore()
repo = babygit.repo.Repo(s)

class UrlCtx:
    def __init__(self, basefn, instream = None):
        logging.debug('basefn = ' + basefn)
        self.base = os.path.split(basefn)[0]
        if self.base.startswith('/'):
            self.base = self.base[1:]
        self.instream = instream
    def resolve(self, url):
        if url.startswith('/'):
            fn = url[1:]
        elif url == '-':
            return self.instream
        else:
            fn = os.path.join(self.base, url)
        logging.debug('opening: ' + fn)
        obj = repo.traverse(fn)
        if obj is None:
            return None
        return StringIO.StringIO(babygit.babygit.obj_contents(obj))

# todo: proofs "upto" functionality, based on split_gh_file