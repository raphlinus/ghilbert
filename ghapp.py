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

from google.appengine.api import users
from google.appengine.ext import webapp
from google.appengine.ext.webapp.util import run_wsgi_app
from google.appengine.ext import db

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
        self.response.out.write('<html><body>')

        proofs = db.GqlQuery("SELECT * FROM Proof ORDER BY date DESC LIMIT 10")

        for proof in proofs:
            if proof.author:
                self.response.out.write('<b>%s</b> wrote ' % proof.author.nickname())
            else:
                self.response.out.write('An anonymous person wrote ')
            self.response.out.write('<a href="/edit/%s">%s</a>:<br />' %
                                    (proof.name, proof.name))
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

        proof.name = self.request.get('name')
        proof.content = self.request.get('content')
        proof.put()
        self.response.out.write('save ok')

class EditPage(webapp.RequestHandler):
    def get(self, name):
        self.response.out.write("""<title>Ghilbert</title>

<body>
<h1>Ghilbert - editing %s</h1>

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
url = '../peano/peano_thms.gh';
uc = new GH.XhrUrlCtx('../', url);
v = new GH.VerifyCtx(uc, run);
run(uc, url, v);

var mainpanel = GH.CanvasEdit.init();
var direct = new GH.Direct(mainpanel, document.getElementById('stack'));
direct.vg = v;
""" % name);
        self.response.out.write('name = %s;\n' % `name`)
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
        if arg is not None:
            print 'arg = ' + arg + '<br />\n'
        for name in os.environ.keys():
            self.response.out.write("%s = %s<br />\n" % (name, os.environ[name]))

class MainPage(webapp.RequestHandler):
    def get(self):
        self.response.out.write("""<title>Ghilbert main</title>
<body>
<h1>Ghilbert main</h1>""")
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
