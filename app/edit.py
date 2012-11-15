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

# Handlers for editing proofs

import cgi
import logging
import StringIO
import urllib

import webapp2
from webapp2_extras import json

import verify

import common
import read
import textutils
import users

import babygit.appengine
import babygit.repo
import babygit.stage

s = babygit.appengine.AEStore()

# Retrieves a prefix of a proof file, up to the named theorem. This logic is
# likely to move into the client, but for now it's a fairly straightforward
# adaptation of the older logic.
class UptoHandler(webapp2.RequestHandler):
    def __init__(self, request, response):
        self.initialize(request, response)
        self.store = s
        self.repo = babygit.repo.Repo(s)

    def get(self, arg):
        o = self.response.out
        asplit = arg.rsplit('/', 1)
        if len(asplit) < 2:
            o.write('error: expected proof_file.gh/thmname')
            return
        url = '/' + asplit[0]
        thmname = asplit[1]
        urlctx = read.UrlCtx(url)
        text = urlctx.resolve(url)
        if text is None:
            o.write('error: didn\'t find url: ' + url)
            return
        lines = text.readlines()
        digest = textutils.split_gh_file(lines)
        digestd = dict(digest)
        if digestd.has_key(thmname):
            start, end = digestd[thmname]
            lines = lines[:start]
        self.response.headers['Content-Type'] = 'text/plain'
        o.write(''.join(lines))

class EditHandler(users.AuthenticatedHandler):
    def __init__(self, request, response):
        self.initialize(request, response)
        self.store = s
        self.repo = babygit.repo.Repo(s)

    def get(self, arg):
        o = self.response.out
        asplit = arg.rsplit('/', 1)
        if len(asplit) < 2:
            o.write('expected proof_file.gh/thmname')
            return
        url = '/' + asplit[0]
        thmname = asplit[1]
        urlctx = read.UrlCtx(url)
        text = urlctx.resolve(url)
        if text is None:
            o.write('Well, didn\'t find url: ' + url)
            return
        lines = text.readlines()
        digest = textutils.split_gh_file(lines)
        digestd = dict(digest)
        logging.debug(`(thmname, json.encode(thmname), urllib.quote(arg))`)
        if self.userobj:
            auth = 'Logged in as ' + cgi.escape(self.userobj.identity)
            if self.has_write_perm:
                auth += ', ok to save.'
            else:
                auth += ', but no save permissions.'
        else:
            auth = 'Not logged in, save won\'t work.'
        o.write("""<head>
<title>Ghilbert</title>
<style type="text/css">
    #panel tr.headerRow {background-color: #ccc}
    #panel tr.clickableRow {cursor: pointer}
    #panel tr.clickableRow:hover {background-color: #eee}
    #panel tr.clickableRow:active {background-color: #ddd}
    table#panel { border: 1px solid black; border-collapse:collapse;}
    #panel tr { border: 1px solid black; }
    #panel td {padding: .3em; }

</style>
</head>
        

<body>
<a href="/">Home</a> <a href="/recent">Recent</a>
<h1>Ghilbert - editing <em id="thmname"></em></h1>

<script src="/js/verify.js" type="text/javascript"></script>
<script src="/js/sandbox.js" type="text/javascript"></script>
<script src="/js/inputlayer.js" type="text/javascript"></script>
<script src="/js/edit.js" type="text/javascript"></script>
<script src="/js/direct.js" type="text/javascript"></script>
<script src="/js/panel.js" type="text/javascript"></script>
<script src="/js/typeset.js" type="text/javascript"></script>

<p>
<div style="display:block;float:left">
  <label for="number">before: </label><input type="text" id="number" value="%s"/>  <a href="#" id="small" onclick="GH.setSize(0)">small</a> <a href="#" id="medium" onclick="GH.setSize(1)">medium</a> <a href="#" id="large" onclick="GH.setSize(2)">large</a> 
<br/>
  <textarea id="canvas" cols="80" rows="20" width="640" height="480" tabindex="0"></textarea><br/>
  <input type="button" id="save" onclick="GH.save(document.getElementById('canvas').value, url)" name="save" value="save"/>
  <input type="button" id="saveDraft" onclick="GH.saveDraft(document.getElementById('canvas').value)" name="save draft" value="save draft"/>
  <span id="saving"></span>
<br/>
  <a href="#" id="autounify" style="display:none">autounify</a><br/>
  <div id="stack">...</div>
</div>
<div width="400" height="800" style="display:block;float:left">
  <button id="inferences">Inference</button>
  <button id="deductions">Deduction</button>
  <button id="unified">Unified</button>
  <label for="filter">filter: </label><input type="text" id="filter"/>
  <br/>
  <table id="panel" border="1" style="border:1px solid;">
  </table>
</div>
<div id="output" style="clear:left;"></div>
<p>%s</p>
<script type="text/javascript">

name = %s;
GH.Direct.replace_thmname(name);
GH.updatemultiline([], document.getElementById('stack'));

url = %s;
// TODO: better handling of raw urls (ideally draw from a specific commit)
uc = new GH.XhrUrlCtx('/', '/git' + url);
v = new GH.VerifyCtx(uc, run);
v.set_suppress_errors(true);
run(uc, '/proofs_upto/%s', v);
v.set_suppress_errors(false);

var mainpanel = new GH.TextareaEdit(document.getElementById('canvas'));
//var mainpanel = GH.CanvasEdit.init();
window.direct = new GH.Direct(mainpanel, document.getElementById('stack'));
window.direct.vg = v;
var number = document.getElementById('number');
number.onchange = function() {
    var uc = new GH.XhrUrlCtx('/', '/git' + url);
    var v = new GH.VerifyCtx(uc, run);
    v.set_suppress_errors(true);
    run(uc, '/proofs_upto' + url + '/' + number.value, v);
    v.set_suppress_errors(false);
    window.direct.vg = v;
    window.direct.update();
};
var panel = new GH.Panel(window.direct.vg);
""" % (thmname, auth, json.encode(thmname), json.encode(url), urllib.quote(arg)))
        if digestd.has_key(thmname):
            start, end = digestd[thmname]
            thmbody = lines[start:end]
            thmbody = [l.rstrip() for l in thmbody]
            result = json.encode(thmbody)
            o.write('mainpanel.setLines(%s);\n' % result)
        o.write('</script>\n')

def skip_blank_lines(index, lines):
    while index < len(lines) and lines[index].rstrip() == '':
        index += 1
    return index

class ErrorHandler:
    def __init__(self):
        self.first_error = None
        self.fatal_error = False
    def error_handler(self, label, msg):
        if self.first_error is None:
            self.first_error = (label, msg)
        if label == '':
            # Errors that happen inside theorem contexts can be recovered. This roughly
            # corresponds to being able to continue (-c in the command line).
            self.fatal_error = True
        return True

class SaveHandler(users.AuthenticatedHandler):
    def __init__(self, request, response):
        self.initialize(request, response)
        self.store = s
        self.repo = babygit.repo.Repo(s)

    def post(self):
        if not self.has_write_perm:
            return common.error_403(self)

        name = self.request.get('name')
        content = self.request.get('content')
        number = self.request.get('number')
        url = self.request.get('url')
        logging.debug(`url`)

        # TODO: validate the name a bit more (no / or space)

        # Edit the content into the theorem text. This is probably best done
        # client-side, but for now we'll stick with the way it worked before.

        logging.debug(`(name, content, number)`)
        urlctx = read.UrlCtx(url)
        text = urlctx.resolve(url)
        if text is None:
            lines = []
        else:
            lines = text.readlines()
        digest = textutils.split_gh_file(lines)
        digestd = dict(digest)
        # Insert before number, or at end of file if not found
        if len(digest) == 0:
            insertpt = len(lines)
        elif digestd.has_key(number):
            insertpt = digestd[number][0]
        else:
            insertpt = skip_blank_lines(digest[-1][1][1], lines)
        if digestd.has_key(name):
            start, end = digestd[name]
            end = skip_blank_lines(end, lines)
            lines[start:end] = []
            if insertpt >= end:
                insertpt -= end - start
        contentlines = content.split('\n')
        while len(contentlines) > 0 and contentlines[-1].rstrip() == '':
            contentlines.pop()
        if len(contentlines) > 0:
            if insertpt > 0 and lines[insertpt - 1].rstrip() != '':
                contentlines.insert(0, '\n')
            contentlines.append('')
        lines[insertpt:insertpt] = contentlines
        lines = [line.rstrip() for line in lines]
        newcontent = '\n'.join(lines)
        if isinstance(newcontent, unicode): newcontent = newcontent.encode('utf-8')

        o = self.response.out

        # Verify
        pipe = StringIO.StringIO(newcontent)
        urlctx = read.UrlCtx(url, pipe)
        error_handler = ErrorHandler()
        ctx = verify.VerifyCtx(urlctx, verify.run, error_handler.error_handler)
        tmpout = StringIO.StringIO()
        ctx.run(urlctx, '-', ctx, tmpout)
        logging.debug(`tmpout.getvalue()`)
        if error_handler.fatal_error:
            # TODO: plumb actual error message
            o.write(json.encode(['error', error_handler.first_error[1]]))
            return

        # Now save the new text
        git_path = str(url)
        if git_path.startswith('/'): git_path = git_path[1:]
        babygit.stage.checkout(self.repo)
        tree = babygit.stage.save(self.repo, git_path, newcontent)
        babygit.stage.add(self.repo, tree)
        author = self.userobj.identity
        msg = 'Commit from web thm editor: save ' + name + '\n'
        commitsha = babygit.stage.commit(self.repo, author, msg)
        o.write(json.encode(['ok', 'successfully saved ' + name]))
