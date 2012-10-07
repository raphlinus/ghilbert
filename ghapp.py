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

# This is the main AppEngine content handler for serving Ghilbert.

import cgi
import urllib
import logging
import StringIO

import verify
import showthm
import babygit.web
import app.wiki

from google.appengine.api import users
from google.appengine.ext import webapp
from google.appengine.ext.webapp.util import run_wsgi_app
from google.appengine.ext import db

from django.utils import simplejson

# Only supports strings and lists now.
def json_dumps(obj):
    if type(obj) in (str, unicode):
        obj = obj.replace('\\', '\\\\')
        obj = obj.replace('"', '\\"')
        return '"' + obj + '"'
    elif type(obj) == list:
        return "[" + ", ".join(map(json_dumps, obj)) + "]"
    else:
        return 'null'

# Return a stream over all proofs in the repository, including the base peano set.
# The proofs are ordered by number.  Optionally, you may provide one proof to be replaced.
# TODO: this probably doesn't have to all be in memory at once.
# TODO: this also shouldn't query the entire DB and sort.
def get_all_proofs(replacing=None, below=None):
    pipe = StringIO.StringIO()
    for line in open('peano/peano_thms.gh', 'r'):
        pipe.write(str(line))

    q = Proof.all()
    q.order('number')
    written = (replacing is None)
    for proof in q:
        if below is not None and proof.number >= below:
            break    
        if not written and proof.number > replacing.number:
            pipe.write(str(replacing.content))
            written = True
        if replacing is None or proof.name != replacing.name:
            pipe.write("# number %s\n" % str(proof.number))
            if proof.content is None:
                pipe.write("# proof.content is None\n")
            else:
                pipe.write(str(proof.content))
                pipe.write("\n")
    if not written:
        pipe.write(str(replacing.content))
    pipe.seek(0)
    return pipe

class Proof(db.Model):
    author = db.UserProperty()
    name = db.StringProperty()
    content = db.TextProperty()
    date = db.DateTimeProperty(auto_now=True)
    number = db.FloatProperty()
    
class Greeting(db.Model):
    author = db.UserProperty()
    content = db.StringProperty(multiline=True)
    date = db.DateTimeProperty(auto_now_add=True)

class RecentPage(webapp.RequestHandler):
    def get(self):
        self.response.out.write("""<html><body>
<p>Recent saves:</p>""")

        proofs = db.GqlQuery("SELECT * FROM Proof ORDER BY date DESC LIMIT 10")

        for proof in proofs:
            if proof.author:
                self.response.out.write('<b>%s</b> wrote ' % proof.author.nickname())
            else:
                self.response.out.write('An anonymous person wrote ')
            self.response.out.write('<a href="/edit/%s">%s</a>:<br />' %
                                    (urllib.quote(proof.name),
                                     cgi.escape(proof.name)))
            if (proof.content is None):
                content = ""
            else:
                content = cgi.escape(proof.content)
            newcontent = []
            for line in content.rstrip().split('\n'):
                sline = line.lstrip()
                newcontent.append('&nbsp;' * (len(line) - len(sline)) + sline)
            content = '<br />'.join(newcontent)
            self.response.out.write('<blockquote>%s</blockquote>' % content)

class SaveHandler(webapp.RequestHandler):
    def post(self):
        # Note, the following line gets the un-url-encoded name.
        name = self.request.get('name')
        proof = Proof.get_or_insert(name)
        proof.name = name
        proof.content = self.request.get('content')
        proof.number = float(self.request.get('number'))

        if users.get_current_user():
            proof.author = users.get_current_user()


        self.response.out.write("Verifying:\n")
        pipe = get_all_proofs(replacing=proof)
        url = '-'
        urlctx = verify.UrlCtx('','peano/peano_thms.gh', pipe)
        ctx = verify.VerifyCtx(urlctx, verify.run, False)
        ctx.run(urlctx, url, ctx, self.response.out)
        # Accept or reject
        if ctx.error_count > 0:
            self.response.out.write("\nCannot save; %d errors\n" % ctx.error_count)
        else:
            proof.put()
            self.response.out.write("\nsave ok\n")

class EditPage(webapp.RequestHandler):
    def get(self, name):
        if name == '':
            name = 'new%20theorem'
        # name here is URL-encoded, we want to display the unencoded version
        # as text, and avoid the possibility of injection attack.
        name = urllib.unquote(name);
        q = Proof.all()
        q.filter('name =', name)
        q.order('-date')
        proof = q.get()
        if proof and proof.number is not None:
            number = float(proof.number)
        else:
            proofs = db.GqlQuery("SELECT * FROM Proof ORDER BY number DESC LIMIT 1")
            last_proof = proofs.get()
            if (last_proof and last_proof.number is not None):
                number = float(last_proof.number + 1)
            else:
                number = float(1)


        self.response.out.write("""<head>
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
  <label for="number">number: </label><input type="text" id="number" value="%s"/>  <a href="#" id="small" onclick="GH.setSize(0)">small</a> <a href="#" id="medium" onclick="GH.setSize(1)">medium</a> <a href="#" id="large" onclick="GH.setSize(2)">large</a> 
<br/>
  <textarea id="canvas" cols="80" rows="20" width="640" height="480" tabindex="0"></textarea><br/>
  <input type="button" id="save" onclick="GH.save(document.getElementById('canvas').value)" name="save" value="save"/>
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
<script type="text/javascript">

name = %s;
GH.Direct.replace_thmname(name);
GH.updatemultiline([], document.getElementById('stack'));

url = '/peano/peano_thms.gh';
uc = new GH.XhrUrlCtx('/', url);
v = new GH.VerifyCtx(uc, run);
run(uc, '/proofs_upto/%f', v);

var mainpanel = new GH.TextareaEdit(document.getElementById('canvas'));
//var mainpanel = GH.CanvasEdit.init();
window.direct = new GH.Direct(mainpanel, document.getElementById('stack'));
window.direct.vg = v;
var number = document.getElementById('number');
number.onchange = function() {
    var url = '../peano/peano_thms.gh';
    var uc = new GH.XhrUrlCtx('../', url);
    var v = new GH.VerifyCtx(uc, run);
    run(uc, '../proofs_upto/' + number.value, v);
    window.direct.vg = v;
    text.dirty();
};
var panel = new GH.Panel(window.direct.vg);
""" % (number, `name`, number));
        if proof:
            result = json_dumps(proof.content.split('\n'))
            self.response.out.write('mainpanel.setLines(%s);\n' % result)
        self.response.out.write('</script>\n')

from google.appengine.ext import webapp
import os

class PrintEnvironmentHandler(webapp.RequestHandler):
    def get(self, arg):
        self.response.out.write(simplejson.dumps([1, 2]) + "\n")
        if arg is not None:
            print 'arg = ' + arg + '<br />\n'
        for name in os.environ.keys():
            self.response.out.write("%s = %s<br />\n" % (name, os.environ[name]))

class AllProofsPage(webapp.RequestHandler):
    def get(self, number):
        self.response.headers['Content-Type'] = 'text/plain'
        self.response.out.write(get_all_proofs(below=float(number)).getvalue())

class StaticPage(webapp.RequestHandler):
    def get(self, filename):
        try:
            lines = open('peano/%s' % filename)
        except IOError, x:
            self.error(404)
            return
        self.response.headers['Content-Type'] = 'text/plain'
        for line in lines:
            self.response.out.write(line)

class MainPage(webapp.RequestHandler):
    def get(self):
        self.response.out.write("""<title>Ghilbert web app</title>
<body>
<h1>Ghilbert web app</h1>

<p>This is an early prototype of a web app for developing
<a href="http://sites.ghilbert.org/">Ghilbert</a>
proofs.</p>

<p>See above link for basic documentation. Source code for this site
is hosted at <a href="http://ghilbert.googlecode.com/">Google Code</a>.</p>

<p><a href="/recent">Recent saves</a></p>

<p><a href="/listthms">List of all theorems</a></p>
""")
        user = users.get_current_user()
        if user:
            self.response.out.write('<p>Logged in as ' + user.nickname() + '\n')
        self.response.out.write('<p><a href="%s">login</a>' %
                                users.create_login_url('/'))

urlmap = [
    ('/', MainPage),
    ('/recent', RecentPage),
    ('/peano/(.*\.gh)', StaticPage),
    ('/peano/(.*\.ghi)', StaticPage),
    ('/proofs_upto/(.*)', AllProofsPage),
    ('/edit/(.*)', EditPage),
    ('/env(/.*)?', PrintEnvironmentHandler),
    ('/showthm/(.*)', showthm.ShowThmPage),
    ('/listthms(/.*)?', showthm.ListThmsPage),
    ('/git/(.*)', babygit.web.handler),
    ('/wiki(/.*)?', app.wiki.Handler),
    ('/save', SaveHandler),

     # TODO: actually plumb namespace
    ('/peano/(.*)', showthm.ShowThmPage),
]


application = webapp.WSGIApplication(urlmap, debug=True)

def main():
    run_wsgi_app(application)

if __name__ == "__main__":
    main()
