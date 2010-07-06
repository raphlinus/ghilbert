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

class Proof(db.Model):
    author = db.UserProperty()
    name = db.StringProperty()
    content = db.TextProperty()
    date = db.DateTimeProperty(auto_now_add=True)

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
            content = cgi.escape(proof.content)
            newcontent = []
            for line in content.rstrip().split('\n'):
                sline = line.lstrip()
                newcontent.append('&nbsp;' * (len(line) - len(sline)) + sline)
            content = '<br />'.join(newcontent)
            self.response.out.write('<blockquote>%s</blockquote>' % content)

class SaveHandler(webapp.RequestHandler):
    def post(self):
        proof = Proof()

        if users.get_current_user():
            proof.author = users.get_current_user()
        # Note, the following line gets the un-url-encoded name.
        name = self.request.get('name')
        # logging.info('Saving "%s"\n', name)
        proof.name = name
        proof.content = self.request.get('content')
        proof.put()
        self.response.out.write('save ok')

class EditPage(webapp.RequestHandler):
    def get(self, name):
        if name == '':
            name = 'new%20theorem'
        # name here is URL-encoded, we want to display the unencoded version
        # as text, and avoid the possibility of injection attack.
        name = urllib.unquote(name);
        self.response.out.write("""<title>Ghilbert</title>

<body>
<a href="/">Home</a> <a href="/recent">Recent</a>
<h1>Ghilbert - editing <em id="thmname"></em></h1>

<script src="/js/verify.js" type="text/javascript"></script>
<script src="/js/sandbox.js" type="text/javascript"></script>
<script src="/js/inputlayer.js" type="text/javascript"></script>
<script src="/js/edit.js" type="text/javascript"></script>
<script src="/js/direct.js" type="text/javascript"></script>
<script src="/js/typeset.js" type="text/javascript"></script>

<p>

<canvas id="canvas" width="640" height="480" tabindex="0"></canvas>
<canvas id="stack" width="640" height="480" tabindex="0"></canvas>

<div id="output">(output goes here)</div>

<script type="text/javascript">

name = %s;
GH.Direct.replace_thmname(name);

url = '/peano/peano_thms.gh';
uc = new GH.XhrUrlCtx('/', url);
v = new GH.VerifyCtx(uc, run);
run(uc, url, v);

var mainpanel = GH.CanvasEdit.init();
var direct = new GH.Direct(mainpanel, document.getElementById('stack'));
direct.vg = v;
""" % `name`);
        q = Proof.all()
        q.filter('name =', name)
        q.order('-date')
        proof = q.get()
        if proof:
            result = json_dumps(proof.content.split('\n'))
            self.response.out.write('mainpanel.text = %s;\n' % result)
            self.response.out.write('mainpanel.dirty();\n');
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
""")
        user = users.get_current_user()
        if user:
            self.response.out.write('<p>Logged in as ' + user.nickname() + '\n')
        self.response.out.write('<p><a href="%s">login</a>' %
                                users.create_login_url('/'))

application = webapp.WSGIApplication(
                                     [('/', MainPage),
                                      ('/recent', RecentPage),
                                      ('/edit/(.*)', EditPage),
                                      ('/env(/.*)?', PrintEnvironmentHandler),
                                      ('/save', SaveHandler)],
                                     debug=True)

def main():
    run_wsgi_app(application)

if __name__ == "__main__":
    main()
