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
from time import gmtime, strftime

from google.appengine.api import users
from google.appengine.ext import webapp
from google.appengine.ext.webapp.util import run_wsgi_app
from google.appengine.ext import db

from django.utils import simplejson

class Player(db.Model):
    name = db.StringProperty()
    lastSeen = db.DateTimeProperty(auto_now=True)
    score = db.IntegerProperty()
    location = db.StringProperty()
    goal = db.StringProperty()
    # JS that sets up the tree-proof environment: operators, theorems, arrow schemes
    setupJs = db.TextProperty()
    # Keys into the GhilbertInterface table; points to which interfaces the user has unlocked.
    ghilbertInterfaces = db.StringListProperty()
    # ghilbert-parsable text for the player's theorems
    ghilbertText = db.TextProperty()
    # Log of all actions
    log = db.TextProperty()
    
class StatusJs(webapp.RequestHandler):
    def get(self, playerName):
        player = Player.get_or_insert(key_name=playerName)
        tip = '"Welcome back."';
        if (player.location is None):
            player.score = 0
            player.location = "PropCal1"
            player.goal="(&#x2192; A (&#x2192; B B))"
            player.name = playerName
            player.log = "### Created " + strftime("%a, %d %b %Y %H:%M:%S +0000", gmtime())
            player.setupJs = """
GHT.Operators = {};
GHT.Thms = {};
GHT.ArrowScheme = {};
GHT.DisabledOptions = {};
GHT.Operators["->"] = new Operator("->","\u2192","wff",["wff","wff"],[-1,1]);
GHT.Thms["ax-simplify"] = T(O("->"),TV("wff", -1),T(O("->"),TV("wff", -2),TV("wff", -1)));
GHT.Thms["ax-distribute"] = T(O("->"),T(O("->"),TV("wff", -1),T(O("->"),TV("wff", -2),TV("wff", -3))),T(O("->"),T(O("->"),TV("wff", -1),TV("wff", -2)),T(O("->"),TV("wff", -1),TV("wff", -3))));
GHT.ArrowScheme["mp"] = ["ax-mp", "ax-mp"]; //TODO: what does this second ax-mp really mean? why does that work?
GHT.ArrowScheme["->"] = ["imim1i", "imim2i"];
GHT.DisabledOptions.generify = 1;
GHT.DisabledOptions.equivalents = 1;
GHT.DisabledOptions.initials = 1;
GHT.DisabledOptions["term substitute"] = 1;
GHT.DisabledOptions.terminals = 1;
GHT.setProof((new GHT.ProofFactory()).newProof("ax-simplify"));

"""
            player.ghilbertInterfaces = ["PosPropCal"]
            player.ghilbertText = """
import (POSPROPCAL PosPropCal () "")
tvar (wff A B C D E F G H)
"""

            tip = '"Welcome!  I see you\'re new here.  Feel free to click around and explore.  You can\'t mess up."'
            player.put()
        self.response.out.write("""
%s

GHT.Tip.set("welcome", %s);

({
score: %s,
location: "%s",
goal: "%s",
name: "%s",
})
"""
                                % (player.setupJs, tip, player.score, player.location, player.goal, player.name));


class SaveHandler(webapp.RequestHandler):
    def post(self):
        # Note, the following line gets the un-url-encoded name.
        playerName = self.request.get('playerName')
        player = Player.get_by_key_name(playerName)
        if (player is None):
            self.response.out.write("GHT.Tip.set('You need a name if you want your saves to last!');")
        else:
            pass
        interfaces = {'PosPropCal':"""
# positive propositional calculus
kind (wff)
tvar (wff A B C D E F G H)
term (wff (-> A B))
stmt (ax-simplify () () (-> A (-> B A)))
stmt (ax-distribute () () (-> (-> A (-> B C)) (-> (-> A B) (-> A C))))
stmt (ax-mp () (A (-> A B)) B)
#TODO: these are provable from above... reduce the interface?
stmt (imim1i () ((-> A B)) (-> (-> B C) (-> A C)))
stmt (imim2i () ((-> A B)) (-> (-> C A) (-> C B)))
"""
                      }
        proofText = player.ghilbertText + "\n" + self.request.get('proof') + "\n"
        output = StringIO.StringIO();
        output.write("Verifying: \n===\n%s\n===\n" % proofText);
        interfaces["-"] = proofText;
        urlctx = verify.DictionaryCtx(interfaces)
        ctx = verify.VerifyCtx(urlctx, verify.run, False)
        ctx.run(urlctx, '-', ctx, output)
        if ctx.error_count > 0:
            self.response.out.write("GHT.Tip.set('saveError', 'Cannot save!');\n/*\n%s\n*/" % output.getvalue())
        else:
            self.response.out.write("GHT.Tip.set('saved');\n")
            player.ghilbertText = proofText;
            player.log += "\n# %s\n%s\n" % (strftime("%a, %d %b %Y %H:%M:%S +0000", gmtime()),
                                            self.request.get('log'))
            player.setupJs += "GHT.Thms['%s'] = %s;\n" % (self.request.get('thmName'), self.request.get('source'))
            player.put()

application = webapp.WSGIApplication(
                                     [('/tree/status/(.*)', StatusJs),
                                      ('/tree/save', SaveHandler),
                                      ],
                                     debug=True)

def main():
    run_wsgi_app(application)

if __name__ == "__main__":
    main()
