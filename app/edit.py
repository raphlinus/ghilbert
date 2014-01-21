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
        self.response.headers['Content-Type'] = 'text/plain; charset=UTF-8'
        o.write(''.join(lines))

class EditHandler(users.AuthenticatedHandler):
    def __init__(self, request, response):
        self.initialize(request, response)
        self.store = s
        self.repo = babygit.repo.Repo(s)

    def get(self, arg):
        o = self.response.out
        useAce = self.request.get("ace")
        asplit = arg.rsplit('/', 1)
        if len(asplit) < 2:
            o.write('expected proof_file.gh/thmname')
            return
        url = '/' + asplit[0]
        thmname = asplit[1]
        urlctx = read.UrlCtx(url)
        text = urlctx.resolve(url)
        if text is None:
            o.write('Well, didn\'t find url: ' + url + '. ')
            ghiFile = '/' + asplit[0] + 'i'
            o.write('Unfortunately, the axioms (statements without proofs) are not set up ')
            o.write('properly and end up here. ')
            o.write('Maybe try the ghi file: <a href="' + ghiFile + '">' + ghiFile + '</a>')
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
        elif users.bypass_local_auth(self.request):
            auth = 'Not logged in, but local dev server.'
        else:
            auth = 'Not logged in, save won\'t work.'
        o.write("""<head>
<title>Edit</title>
<link rel=stylesheet href="/static/editor.css" type="text/css">
<link rel=stylesheet href="/static/prover.css" type="text/css">
<link rel=stylesheet href="/static/common.css" type="text/css">
<style type="text/css">
""")
        if useAce: o.write("""    .ace_marker-layer .gh_error {
        position: absolute;
        z-index: 4;
        background-color: #fcc;
    }
</style>
<style type="text/css" media="screen">
    #canvas { 
        position: relative;
        width: 600px;
        height: 400px;
    }
""")
        o.write("""</style>
</head>
        

<body class="stack-mode">
""")
        o.write('<div class="header">')
        o.write('  <a href="/"><img src="/static/logo.png" style="position:absolute;"/></a>')
        o.write('  <span id="header-boxes">');
        o.write("""    <span class="header-box dictionary-entry" onclick="GH.Panel.setPanelNum(3)">dictionary</span> """);
        o.write('  </span>');
        o.write('</div>')
        o.write('<span id="authetication">%s</span>' % auth);
        o.write("""
<script src="/js/verify.js" type="text/javascript"></script>
<script src="/js/sandbox.js" type="text/javascript"></script>
<script src="/js/inputlayer.js" type="text/javascript"></script>
<script src="/js/edit.js" type="text/javascript"></script>
<script src="/js/direct.js" type="text/javascript"></script>
<script src="/js/proofstep.js" type="text/javascript"></script>
<script src="/js/proofsegment.js" type="text/javascript"></script>
<script src="/js/prover/prover.js" type="text/javascript"></script>
<script src="/js/prover/archiveSearcher.js" type="text/javascript"></script>
<script src="/js/prover/buttonController.js" type="text/javascript"></script>
<script src="/js/prover/equalizer.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/evaluator.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/add.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/and.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/apply.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/constant.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/div.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/divides.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/elementOf.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/equality.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/exponent.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/factorial.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/fibonacci.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/greaterThan.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/greaterThanEqual.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/halfminus.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/ifn.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/intersection.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/interval.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/lessThan.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/lessThanEqual.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/modulo.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/multiply.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/negative.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/product.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/properSubset.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/prime.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/setEquality.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/subset.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/substitution.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/successor.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/sum.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/triangle.js" type="text/javascript"></script>
<script src="/js/prover/evaluator/union.js" type="text/javascript"></script>
<script src="/js/prover/theorem/attachDecorator.js" type="text/javascript"></script>
<script src="/js/prover/theorem/baseTheorem.js" type="text/javascript"></script>
<script src="/js/prover/theorem/commuteDecorator.js" type="text/javascript"></script>
<script src="/js/prover/theorem/inferDecorator.js" type="text/javascript"></script>
<script src="/js/prover/theorem/deduceDecorator.js" type="text/javascript"></script>
<script src="/js/prover/theorem/theoremFactory.js" type="text/javascript"></script>
<script src="/js/prover/theorem/theoremWriter.js" type="text/javascript"></script>
<script src="/js/prover/remover.js" type="text/javascript"></script>
<script src="/js/prover/replacer.js" type="text/javascript"></script>
<script src="/js/prover/multiReplacer.js" type="text/javascript"></script>
<script src="/js/prover/conditionalReplacer.js" type="text/javascript"></script>
<script src="/js/prover/existGeneralizer.js" type="text/javascript"></script>
<script src="/js/prover/instantiator.js" type="text/javascript"></script>
<script src="/js/prover/repositioner.js" type="text/javascript"></script>
<script src="/js/prover/symbolTree.js" type="text/javascript"></script>
<script src="/js/prover/numUtil.js" type="text/javascript"></script>
<script src="/js/prover/setUtil.js" type="text/javascript"></script>
<script src="/js/prover/tupleUtil.js" type="text/javascript"></script>
<script src="/js/prover/operatorUtil.js" type="text/javascript"></script>
<script src="/js/prover/variableGenerator.js" type="text/javascript"></script>
<script src="/js/panel.js" type="text/javascript"></script>
<script src="/js/typeset.js" type="text/javascript"></script>

<div id="editor-body">
<div id="dictionary">
    <div style="overflow:hidden" "border-right: 1px solid #bbb">
        <div class="section-title">Dictionary</div>
        <button id="inferences">Inference</button>
        <button id="deductions">Deduction</button>
        <button id="unified">Unified</button>
        <span class="section-close" onclick="GH.Panel.setPanelNum(2)">X</span>
        <span style="float: right">
            <label for="filter">filter: </label><input type="text" id="filter" class="minor-input"/>
        </span>
    </div>
    <div id="panel-container" style="display:block;float:left">
        <table id="panel" border="1" style="border:1px solid;">
        </table>
    </div>
</div>

<div id="editor-section">
  <span class="section-title">Editor</span>
  <label for="number">before: </label><input type="text" id="number" value="%s" class="minor-input"/>
""" % thmname)
        o.write("""<span class="section-close" onclick="GH.Panel.setPanelNum(1)">X</span>""")
        o.write("""
  <span id="saving"></span>
  <input type="button" id="save" onclick="log(mainpanel); GH.save(window.mainpanel.getValue(), url)" name="save" value="save"/>
  <input type="button" id="exp-adder" onclick="window.direct.prover.openExpAdder()" name="numberAdder" value="Add"/>
<br/>
""")
        if useAce: o.write("""<div id="canvas"></div>
<script src="//d1n0x3qji82z53.cloudfront.net/src-min-noconflict/ace.js" type="text/javascript" charset="utf-8"></script>
<script>
  var editor = ace.edit("canvas");
  </script>
""")
        else:
            o.write('<textarea id="canvas" cols="60" rows="20" width="640" height="480" tabindex="0"></textarea><br/>\n')
        o.write("""
  <a href="#" id="autounify" style="display:none">autounify</a><br/>
</div>
<div id="right-panel">
  <div class="thmtitle">
    <span id="thmname"></span>
    <span class="edit-entry" onclick="GH.Panel.setPanelNum(2)">edit</span>
  </div>
  <div id="stack">...</div>
  <div id="suggest"></div>
</div>
<div id="output" style="clear:left;"></div>
<script type="text/javascript">

name = %s;
GH.Direct.replace_thmname(name);

url = %s;
// TODO: better handling of raw urls (ideally draw from a specific commit)
uc = new GH.XhrUrlCtx('/', '/git' + url);
v = new GH.VerifyCtx(uc, run);
""" % (json.encode(thmname), json.encode(url)))
        if url[-4:] != '.ghi':
            o.write("""
v.set_suppress_errors(true);
run(uc, '/proofs_upto/%s', v);
v.set_suppress_errors(false);

""" % (urllib.quote(arg)))
        if useAce:
            o.write('window.mainpanel = new GH.AceEdit(editor);\n')
        else:
            o.write("window.mainpanel = new GH.TextareaEdit(document.getElementById('canvas'));\n")
        o.write("""window.direct = new GH.Direct(window.mainpanel, document.getElementById('stack'), document.getElementById('suggest'));
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
""")
        if digestd.has_key(thmname):
            start, end = digestd[thmname]
            thmbody = lines[start:end]
            thmbody = [l.rstrip() for l in thmbody]
            result = json.encode(thmbody)
            o.write('window.mainpanel.setLines(%s);\n' % result)
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
        author = self.identity
        msg = 'Commit from web thm editor: save ' + name + '\n'
        commitsha = babygit.stage.commit(self.repo, author, msg)
        o.write(json.encode(['ok', 'successfully saved ' + name]))
