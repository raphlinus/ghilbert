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

# Web handlers for wiki interaction - rendering, editing, etc

from google.appengine.ext import webapp

import cgi
import urllib

import ghmarkup
import babygit.babygit
import babygit.appengine
import babygit.repo
import babygit.stage

s = babygit.appengine.AEStore()
babygit.babygit.ensure_repo(s)

class Handler(webapp.RequestHandler):
    def __init__(self):
        self.store = s
        self.repo = babygit.repo.Repo(s)

    def git_path(self, wiki_path):
        while wiki_path.startswith('/'):
            wiki_path = wiki_path[1:]
        return 'wiki/' + wiki_path

    def get_wiki(self, arg):
        editurl = '/wiki/edit/' + arg
        o = self.response.out
        obj = self.repo.traverse(self.git_path(arg))
        if obj is not None:
            contents = babygit.babygit.obj_contents(obj)
            o.write('''<html><head>
<title>Ghilbert wiki: %s</title>
<body>
<h1>Ghilbert wiki: %s</h1>
''' % (cgi.escape(arg), cgi.escape(arg)))
            o.write(ghmarkup.process_ghmarkup(contents, '/'))
            o.write('<div><a href="%s">Edit</a></div>\n' % urllib.quote(editurl))
        else:
            o.write('<p>No page yet for ' + cgi.escape(arg) + ', but you can <a href="' + editurl + '">create</a> one.</p>')

    def serve_edit(self, editurl, preview = None):
        if preview is None:
            obj = self.repo.traverse(self.git_path(editurl))
            if obj is None:
                action = 'Creating'
                contents = ''
            else:
                action = 'Editing'
                contents = babygit.babygit.obj_contents(obj)
        else:
            action = 'Preview of'
            contents = preview
        o = self.response.out
        title = action + ' wiki page: ' + cgi.escape(editurl)
        o.write('<html><title>' + title + '</title>\n')
        o.write('<body><h1>' + title + '</h1>\n')
        if preview is not None:
            o.write(ghmarkup.process_ghmarkup(contents, '/'))
        o.write('<form method="post" action="/wiki/save/' + urllib.quote(editurl) + '">\n')
        o.write('<textarea cols="80" rows="24" name="content">')
        for line in contents.rstrip().split('\n'):
            o.write(cgi.escape(line) + '\n')
        o.write('</textarea>\n')
        o.write('<br >\n')
        o.write('Commit msg: <input type="text" name="msg" size="65">\n')
        o.write('<br >\n')
        o.write('<input type="submit" name="preview" value="Preview">\n')
        o.write('<input type="submit" name="save" value="Save">\n')
        # TODO: include last commit sha (this is basically a checkout)

    def serve_save(self, path, content, msg):
        babygit.stage.checkout(self.repo)
        content = content.replace('\r', '')
        if isinstance(content, unicode): content = content.encode('utf-8')
        git_path = self.git_path(path)
        tree = babygit.stage.save(self.repo, git_path, content)
        babygit.stage.add(self.repo, tree)
        author = 'Webapp user <anonymous@ghilbert.org>'
        msg = msg.rstrip() + '\n'
        commitsha = babygit.stage.commit(self.repo, author, msg)
        o = self.response.out
        url = '/wiki/' + path
        o.write('Succesfully saved <a href="' + url + '">' + cgi.escape(path) + '</a>')

    def get(self, arg):
        if arg is None or arg == '' or arg == '/':
            path = 'MainPage'
        else:
            path = arg[1:]
        if path.startswith('edit/'):
            return self.serve_edit(path[5:])
        return self.get_wiki(path)

    def post(self, arg):
        if arg.startswith('/save/'):
            if self.request.get('preview'):
                return self.serve_edit(arg[6:], self.request.get('content'))
            if self.request.get('save'):
                return self.serve_save(arg[6:], self.request.get('content'), self.request.get('msg'))

