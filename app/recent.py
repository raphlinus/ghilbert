# Copyright 2010 Google Inc.
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

# Display recent commits

import cgi
import datetime
import urllib
import webapp2

import babygit.appengine
import babygit.repo

import common

s = babygit.appengine.AEStore()
repo = babygit.repo.Repo(s)

def gitpath_to_url(gitpath):
    if gitpath.startswith('wiki/') and gitpath.endswith('.ghm'):
        return '/' + gitpath[:-4]
    else:
        return '/' + gitpath

class RecentChangesPage(webapp2.RequestHandler):
    def __init__(self, request, response):
        self.initialize(request, response)
        self.store = s
        self.repo = repo

    def get(self):
        o = self.response.out
        common.header(o, 'Recent changes')
        o.write('<dl>\n')
        sha = self.repo.gethead()
        max_recent = 20
        for i in range(max_recent):
            commitobj = self.repo.getobj(sha)
            commit = self.repo.parse_commit(commitobj)
            committersplit = commit['committer'].rstrip().rsplit(' ', 2)
            committer = committersplit[0]
            committimestamp = int(committersplit[1])
            committime = datetime.datetime.fromtimestamp(committimestamp)
            o.write('<dt>Commit by ' + cgi.escape(committer) + ', ' + str(committime ) + ':</dt>\n')
            if len(commit['parents']) == 0:
                break
            parentsha = commit['parents'][0]
            parentobj = self.repo.getobj(parentsha)
            parent = self.repo.parse_commit(parentobj)
            diff = self.repo.diff_tree(parent['tree'], commit['tree'])
            for fn, change in diff:
                if change == 'add':
                    changehtml = '+'
                elif change == 'delete':
                    changehtml = '-'
                elif change == 'change':
                    changehtml = '+/-'

                url = gitpath_to_url(fn)
                o.write('<dd><a href="' + urllib.quote(url) + '">' + cgi.escape(fn) + '</a> ' + changehtml + '</dd>\n')
            sha = parentsha
