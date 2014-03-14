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

import webapp2

import cgi
import urllib

import common
import ghmarkup
import gitcontent
import users

import babygit.babygit
import babygit.appengine
import babygit.repo
import babygit.stage

class Handler(users.AuthenticatedHandler):
    def __init__(self, request, response):
        self.initialize(request, response)
        self.repo = gitcontent.get_repo()

    def get_wiki(self, arg):
        editurl = '/wiki/edit/' + arg
        o = self.response.out
        obj = self.repo.traverse(gitcontent.wiki_to_git_path(arg))
        if obj is not None:
            contents = babygit.babygit.obj_contents(obj)
            common.header(o, "")
            o.write('<script type="text/javascript">GH={};</script>')
            o.write('<script src="/js/typeset.js" type="text/javascript"></script>')
            o.write('<script src="/js/sexpression.js" type="text/javascript"></script>')
            o.write('<script src="/js/prover/numUtil.js" type="text/javascript"></script>')
            o.write('<script src="/js/prover/setUtil.js" type="text/javascript"></script>')
            o.write('<script src="/js/prover/tupleUtil.js" type="text/javascript"></script>')
            o.write('<script type="text/javascript"')
            o.write('  src="http://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML">')
            o.write('</script>')
            o.write('<div id="text-body">')
            # o.write("Ghilbert wiki: " + arg)
            o.write(ghmarkup.process_ghmarkup(contents, '/'))
            if self.has_write_perm:
                o.write('<div><a href="%s">Edit</a></div>\n' % urllib.quote(editurl))
            else:
                o.write('<div><a href="/account/Login">Login to edit</a></div>\n')
            o.write('<script type="text/javascript">GH.typeset.formatWiki()</script>')
        else:
            o.write('<p>No page yet for ' + cgi.escape(arg) + ', but you can <a href="' + editurl + '">create</a> one.</p>')

    def serve_edit(self, editurl, preview = None, msg = None):
        if not self.has_write_perm:
            return common.error_403(self)
        if preview is None:
            obj = self.repo.traverse(gitcontent.wiki_to_git_path(editurl))
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
        o.write('<link rel=stylesheet href="/static/wiki.css" type="text/css">')
        o.write('<body><h1>' + title + '</h1>\n')
        if preview is not None:
            o.write(ghmarkup.process_ghmarkup(contents, '/'))
        o.write('<form method="post" action="/wiki/save/' + urllib.quote(editurl) + '">\n')
        o.write('<textarea cols="80" rows="24" name="content">')
        for line in contents.rstrip().split('\n'):
            o.write(cgi.escape(line) + '\n')
        o.write('</textarea>\n')
        o.write('<br >\n')
        o.write('Commit msg: <input type="text" name="msg" size="65"')
        if msg is not None:
            o.write(' value="' + cgi.escape(msg, True) + '"')
        o.write('>\n')
        o.write('<br >\n')
        o.write('<input type="submit" name="preview" value="Preview">\n')
        o.write('<input type="submit" name="save" value="Save">\n')
        # TODO: include last commit sha (this is basically a checkout)

    def serve_save(self, path, content, msg):
        if not self.has_write_perm:
            return common.error_403(self)

        babygit.stage.checkout(self.repo)
        content = content.replace('\r', '')
        if isinstance(content, unicode): content = content.encode('utf-8')
        git_path = gitcontent.wiki_to_git_path(path)
        tree = babygit.stage.save(self.repo, git_path, content)
        babygit.stage.add(self.repo, tree)
        author = self.identity
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
                return self.serve_edit(arg[6:], self.request.get('content'), self.request.get('msg'))
            if self.request.get('save'):
                return self.serve_save(arg[6:], self.request.get('content'), self.request.get('msg'))

