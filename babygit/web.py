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

import appengine
import zlib
import logging
import cgi
import urllib

import babygit
import repo
import stage

from google.appengine.ext import webapp

#s = babygit.FsStore()

s = appengine.AEStore()

def init_test_repo():
    babygit.put_test_repo(s)

    r = repo.Repo(s)
    stage.checkout(r) 
    tree = stage.getroot(r)
    tree = stage.save(r, 'dir/newfile', 'This is a new file!\n', tree)
    tree = stage.save(r, 'dir/anotherfile', 'This is another new file!\n', tree)
    tree = stage.save(r, 'dir/newfile', 'Replace contents\n', tree)
    stage.add(r, tree)
    stage.commit(r, 'Author <author@ghilbert.org>', 'Test adding a new file\n')

class handler(webapp.RequestHandler):
    def __init__(self):
        self.store = s
        self.repo = repo.Repo(s)
    def get(self, arg):
        if arg == 'HEAD':
            self.response.out.write('ref: refs/heads/master\n')
        elif arg == 'info/refs':
            inforefs = s.getinforefs()
            logging.debug(`inforefs`)
            infostr = ''.join(['%s\t%s\n' % (sha, ref) for
                ref, sha in inforefs.iteritems()])
            self.response.out.write(infostr)
        elif arg.startswith('objects/') and arg[10] == '/':
            sha = arg[8:10] + arg[11:49]
            compressed = s.getobjz(sha)
            self.response.headers['Content-Type'] = 'application/octet-stream'
            self.response.out.write(compressed)
        elif arg.startswith('edit/'):
            editurl = arg[5:]
            obj = self.repo.traverse(editurl)
            if obj is None:
                self.response.out.write('404 not found')
            elif babygit.obj_type(obj) == 'blob':
                contents = babygit.obj_contents(obj)
                self.response.out.write('<html><title>Editing: ' + cgi.escape(editurl) + '</title>\n')
                self.response.out.write('<body>\n')
                self.response.out.write('<h1>Editing ' + cgi.escape(editurl) + '</h1>\n')
                self.response.out.write('<form method="post" action="/git/save/' + urllib.quote(editurl) + '">\n')
                self.response.out.write('<textarea cols="80" rows="24" name="content">\n')
                for line in contents.split('\n'):
                    self.response.out.write(cgi.escape(line) + '\n')
                self.response.out.write('</textarea>')
                self.response.out.write('<br />\n')
                self.response.out.write('<input type="submit" value="Save">\n')

        else:
            # try to serve a raw blob
            obj = self.repo.traverse(arg)
            if obj is None:
                self.response.out.write('404 not found')
            elif babygit.obj_type(obj) == 'blob':
                self.response.headers['Content-Type'] = 'text/plain';
                contents = babygit.obj_contents(obj)
                self.response.out.write(contents)
            else:
                ptree = self.repo.parse_tree(obj)
                html = ['<html><ul>']
                for mode, name, sha in ptree:
                    fn = name
                    if mode == '40000': fn += '/'
                    html.append('<li><a href="' + fn + '">' + fn + '</a></li>\n')
                self.response.out.write(''.join(html))

    def post(self, arg):
        if arg.startswith('save/'):
            editurl = arg[5:]
            stage.checkout(self.repo)
            tree = stage.getroot(self.repo)
            tree = stage.save(self.repo, editurl, self.request.get('content'))
            stage.add(self.repo, tree)
            author = 'Author <author@ghilbert.org>'
            msg = 'Commit from wiki\n'
            commitsha = stage.commit(self.repo, author, msg)
            self.response.out.write('saved ' + cgi.escape(editurl) + ' with commit ' + commitsha + '\n')
