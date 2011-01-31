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
import re

from google.appengine.api import users
from google.appengine.ext import webapp
from google.appengine.ext.webapp.util import run_wsgi_app
from google.appengine.ext import db

from django.utils import simplejson

class Goal(db.Model):
    name = db.StringProperty()
    value = db.IntegerProperty()
    next = db.StringProperty()
    ghilbert = db.StringProperty()
    html = db.TextProperty()
    # This text will be appended to the player's ghilbert_text when the theorem is unlocked.
    # Must have one %s which will be replaced by the player's chosen theorem name.
    new_ghilbert = db.TextProperty()
    # Like new_ghilbert, this will be added to the player's setup_js.  It will also be dumped
    # into the response for immediate eval.
    new_js = db.TextProperty()
    # One-time js to be sent only when the goal is achieved.  If none, put up the default tip. 
    update_js = db.TextProperty()
    # TODO: which interfaces are required; which goals are required; branch points
    
#TODO:hack
def get_goal(name):
    goal = Goal.get_or_insert(key_name=name)
    if (name == "PICKUP"):
        name = "anbi2"
    if (True): #goal.name is None
        goal.name = name
        if (name == "idd"):
            goal.next = "id"
            goal.ghilbert = "() () (-> A (-> B B))"
        elif (name == "id"):
            goal.next = "imim2"
            goal.ghilbert = "() () (-> A A)"
        elif (name == "imim2"):
            goal.next = "imim1"
            goal.ghilbert = "() () (-> (-> A B) (-> (-> C A) (-> C B)))" 
        elif (name == "imim1"):
            goal.next = "assertion"
            goal.ghilbert = "() () (-> (-> A B) (-> (-> B C) (-> A C)))" 
        elif (name == "assertion"):
            goal.next = "tie"
            goal.ghilbert = "() () (-> A (-> (-> A B) B))" 
        elif (name == "tie"):
            goal.next = "con12"
            goal.ghilbert = "() () (-> (-> (-> A A) B) B)" 
        elif (name == "con12"):
            goal.next = "contraction"
            goal.ghilbert = "() () (-> (-> A (-> B C)) (-> B (-> A C)))" 
        elif (name == "contraction"):
            goal.next = "fie"
            goal.ghilbert = "() () (-> (-> A (-> A B)) (-> A B))"
            goal.new_ghilbert = """
# %s
import (COREPROPCAL CorePropCal (POSPROPCAL) "")
"""
            goal.new_js = """
// %s
// CorePropCal
GHT.Operators["-."] = new Operator("-.","\u00ac","wff",["wff"],[Infinity]);
GHT.Thms["Transpose"] = T(O("->"),T(O("->"),T(O("-."),TV("wff", -560)),T(O("-."),TV("wff", -571))),T(O("->"),TV("wff", -571),TV("wff", -560)));
GHT.ArrowScheme["-."] = [null];
"""
            goal.update_js = "GHT.Tip.set('notUnlocked');\n"
        elif (name == "fie"):
            goal.next = "notnot2"
            goal.ghilbert = "() () (-> (-. A) (-> A B))"
        elif (name == "notnot1"):
            goal.next = "con3"
            goal.ghilbert = "() () (-> A (-. (-. A)))"
        elif (name == "notnot2"):
            goal.next = "notnot1"
            goal.ghilbert = "() () (-> (-. (-. A)) A)"
        elif (name == "con3"):
            goal.next = "nimp2"
            goal.ghilbert = "() () (-> (-> A B) (-> (-. B) (-. A)))"
            goal.update_js = "GHT.Tip.set('con3Unlocked');\n"
            goal.new_js ="""
// con3
GHT.Operators["-."].bindings[0] = -1;
GHT.ArrowScheme["-."][0] = "%s";
"""
        elif (name == "nimp2"):
            goal.next = "nimp1"
            goal.ghilbert = "() () (-> (-. (-> A B)) (-. B))"
        elif (name == "nimp1"):
            goal.next = "mth8"
            goal.ghilbert = "() () (-> (-. (-> A B)) A)"
        elif (name == "mth8"):
            goal.next = "df-and-just"
            goal.ghilbert = "() () (-> A (-> (-. B) (-. (-> A B))))"
        elif (name == "df-and-just"):
            goal.next = "dfand1"
            goal.ghilbert = "() () (-. (-> (-> A A) (-. (-> B B)))"
            goal.update_js = "GHT.Tip.set('andUnlocked');\n"
            goal.new_js = """
// %s
// And
GHT.Operators["/\\\\"] = new Operator("/\\\\","\u2227","wff",["wff","wff"],[Infinity,Infinity]);
GHT.Thms["Conjoin"] =  T(O("-."),T(O("->"),T(O("->"),T(O("/\\\\"),TV("wff", -360),TV("wff", -361)),T(O("-."),T(O("->"),TV("wff", -360),T(O("-."),TV("wff", -361))))),T(O("-."),T(O("->"),T(O("-."),T(O("->"),TV("wff", -360),T(O("-."),TV("wff", -361)))),T(O("/\\\\"),TV("wff", -360),TV("wff", -361))))));
GHT.ArrowScheme["/\\\\"] = [null, null];
"""
            goal.new_ghilbert = """
defthm (Conjoin wff (/\ A B) () ()
          (-. (-> (-> (/\ A B) (-. (-> A (-. B))))
                  (-. (-> (-. (-> A (-. B))) (/\ A B)))))
     (-. (-> A (-. B)))  (-. (-> A (-. B)))  %s
)
"""
        elif (name == "dfand1"):
            goal.next = "dfand2"
            goal.ghilbert = "() () (-> (/\ A B) (-. (-> A (-. B))))"
        elif (name == "dfand2"):
            goal.next = "anim1"
            goal.ghilbert = "() () (-> (-. (-> A (-. B))) (/\ A B))"
        elif (name == "anim1"):
            goal.next = "anim2"
            goal.ghilbert = "() () (-> (-> A B) (-> (/\ A C) (/\ B C)))"
            goal.update_js = "GHT.Tip.set('anim1Unlocked');\n"
            goal.new_js = """
// anim1
GHT.Operators["/\\\\"].bindings[0] = 1;
GHT.ArrowScheme["/\\\\"][0] = "%s";
"""
        elif (name == "anim2"):
            goal.next = "and1"
            goal.ghilbert = "() () (-> (-> A B) (-> (/\ C A) (/\ C B)))"
            goal.update_js = "GHT.Tip.set('anim2Unlocked');\n"
            goal.new_js = """
// anim2
GHT.Operators["/\\\\"].bindings[1] = 1;
GHT.ArrowScheme["/\\\\"][1] = "%s";
"""
        elif (name == "and1"):
            goal.next = "and2"
            goal.ghilbert = "() () (-> (/\ A B) A)"
        elif (name == "and2"):
            goal.next = "and"
            goal.ghilbert = "() () (-> (/\ A B) B)"
        elif (name == "and"):
            goal.next = "anid"
            goal.ghilbert = "() () (-> A (-> B (/\ A B)))"
        elif (name == "anid"):
            goal.next = "ancom"
            goal.ghilbert = "() () (-> A (/\ A A))"
        elif (name == "ancom"):
            goal.next = "ancr"
            goal.ghilbert = "() () (-> (/\ A B) (/\ B A))"
        elif (name == "ancr"):
            goal.next = "import"
            goal.ghilbert = "() () (-> (-> A B) (-> A (/\ A B))"
        elif (name == "import"):
            goal.next = "anmp"
            goal.ghilbert = "() () (-> (-> A (-> B C)) (-> (/\ A B) C)"
        elif (name == "anmp"):
            goal.next = "anim3"
            goal.ghilbert = "() () (-> (/\ A (-> A B)) B)"
        elif (name == "anim3"):
            goal.next = "prth"
            goal.ghilbert = "() () (-> (/\ A (-> B C)) (-> B (/\ A C)))"
        elif (name == "prth"):
            goal.next = "dfbi"
            goal.ghilbert = "() () (-> (/\ (-> A B) (-> C D)) (-> (/\ A C) (/\ B D)))"
        elif (name == "dfbi"):
            goal.next = "def-bi-1"
            goal.ghilbert = "() () (/\ (-> A A) (-> B B))"
            goal.update_js = "GHT.Tip.set('biUnlocked');\n"
            goal.new_js = """
// %s
// Bi
GHT.Operators["<->"] = new Operator("<->","\u2194","wff",["wff","wff"],[Infinity,Infinity])
GHT.Thms["Equivalate"] =  T(O("/\\\\"),T(O("->"),T(O("<->"),TV("wff", -1),TV("wff", -2)),T(O("/\\\\"),T(O("->"),TV("wff", -1),TV("wff", -2)),T(O("->"),TV("wff", -2),TV("wff", -1)))),T(O("->"),T(O("/\\\\"),T(O("->"),TV("wff", -1),TV("wff", -2)),T(O("->"),TV("wff", -2),TV("wff", -1))),T(O("<->"),TV("wff", -1),TV("wff", -2))));
GHT.ArrowScheme["<->"] = [null, null];
GHT.EquivalenceScheme = {};
"""
            goal.new_ghilbert = """
defthm (Equivalate wff (<-> A B) () ()
     (/\ (-> (<-> A B) (/\ (-> A B) (-> B A)))
         (-> (/\ (-> A B) (-> B A)) (<-> A B)))
    (/\ (-> A B) (-> B A))  (/\ (-> A B) (-> B A))  %s
)
"""
        elif (name == "def-bi-1"):
            goal.next = "def-bi-2"
            goal.ghilbert = "() () (-> (<-> A B) (/\ (-> A B) (-> B A)))"
        elif (name == "def-bi-2"):
            goal.next = "bi1"
            goal.ghilbert = "() () (-> (/\ (-> A B) (-> B A)) (<-> A B))"
        elif (name == "bi1"):
            goal.next = "bi2"
            goal.ghilbert = "() () (-> (<-> A B) (-> A B))"
        elif (name == "bi2"):
            goal.next = "imbi1"
            goal.ghilbert = "() () (-> (<-> A B) (-> B A))"
        elif (name == "imbi1"):
            goal.new_js = '\n GHT.EquivalenceScheme["->"] = ["%s", null]; \n'
            goal.next = "imbi2"
            goal.ghilbert = "() () (-> (<-> A B) (<-> (-> A C) (-> B C)))"
        elif (name == "imbi2"):
            goal.new_js = '\n GHT.EquivalenceScheme["->"][1] = "%s"; \n'
            goal.next = "bibi1"
            goal.ghilbert = "() () (-> (<-> A B) (<-> (-> C A) (-> C B)))"
        elif (name == "bibi1"):
            goal.new_js = '\n GHT.EquivalenceScheme["<->"] = ["%s", null]; \n'
            goal.next = "bibi2"
            goal.ghilbert = "() () (-> (<-> A B) (<-> (<-> A C) (<-> B C)))"
        elif (name == "bibi2"):
            goal.new_js = '\n GHT.EquivalenceScheme["<->"][1] = "%s"; \n'
            goal.next = "mpbi"
            goal.ghilbert = "() () (-> (<-> A B) (<-> (<-> C A) (<-> C B)))"
        elif (name == "mpbi"):
            goal.new_js = '\n GHT.EquivalenceScheme["mp"] = ["%s", null]; \n'
            goal.next = "mpbir"
            goal.ghilbert = "() () (-> A (-> (<-> A B) B))"
        elif (name == "mpbir"):
            goal.new_js = '\n GHT.EquivalenceScheme["mp"][1] = "%s"; \n'
            goal.next = "anbi1"
            goal.ghilbert = "() () (-> A (-> (<-> B A) B))"
        elif (name == "anbi1"):
            goal.new_js = '\n GHT.EquivalenceScheme["/\\\\"] = ["%s", null]; \n'
            goal.next = "anbi2"
            goal.ghilbert = "() () (-> (<-> A B) (<-> (/\ A C) (/\ B C)))"
        elif (name == "anbi2"):
            goal.next = "PICKUP"
            goal.ghilbert = "() () (-> (<-> A B) (<-> (/\ C A) (/\ C B)))"
            goal.new_js = """
GHT.EquivalenceScheme["/\\\\"][1] = "%s";
GHT.Operators["<->"].bindings[1] = [0, 0];
delete GHT.DisabledOptions.equivalents;
"""
        else:
            goal.html = "Sorry, goal '%s' isn't defined yet.  No one thought you'd make it this far!" % name
            return goal
    # TODO: real parser / html formatter
    goal.html = goal.ghilbert[6:].replace(
        "<->", "&#x2194;").replace(
        "-.", "&#x00ac;").replace(
        "/\\", "&#x2227;").replace(
        "->", "&#x2192;")
    goal.value = 1
    goal.put()
    return goal
#TODO: OO
def check_goal(player, proof, thmName, stream):
    goal = get_goal(player.goal)
    if (goal.ghilbert is None):
        return False
    pattern = "thm \([^)]* " + goal.ghilbert.replace("\\","\\\\").replace("(","\(").replace(")","\)")
    if re.match(pattern, proof):
        player.score += goal.value
        if (player.goal == "contraction"):
            player.location = "Outer Procal" #TODO:data driven
        if (goal.new_js):
            player.setupJs += goal.new_js % thmName
            stream.write(goal.new_js % thmName);
        if (goal.new_ghilbert):
            player.ghilbertText += goal.new_ghilbert % thmName
        if (goal.update_js):
            stream.write(goal.update_js)
        else:
            stream.write("GHT.Tip.set('achieved'); // %s\n" % player.goal)
        player.goal = goal.next
        stream.write(player.update_js())
        stream.write("\nGHT.redecorate();\n");
        return True
    stream.write("/*\n MATCH: " + pattern + " #### AGAINST: " + proof + "\n*/\n")
    return False

   
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
    # Javascript for updating the UI to reflect this object's current state
    def update_js(self):
        dict = {};
        for k in ("score", "location", "goal", "name"):
            dict[k] = getattr(self,k);
        dict["goal"] = get_goal(dict["goal"]).html
        return "\nGHT.updateUi('player',%s);\n" % simplejson.dumps(dict)
        
class StatusJs(webapp.RequestHandler):
    def get(self, playerName):
        player = Player.get_or_insert(key_name=playerName)
        tip = '"Welcome back."';
        if (player.location is None):
            player.score = 0
            player.location = "Inner Procal"
            player.goal="idd"
            player.name = playerName
            player.log = "### Created " + strftime("%a, %d %b %Y %H:%M:%S +0000", gmtime())
            player.setupJs = """
GHT.Operators = {};
GHT.Thms = {};
GHT.ArrowScheme = {};
GHT.DisabledOptions = {};
GHT.Operators["->"] = new Operator("->","\u2192","wff",["wff","wff"],[-1,1]);
GHT.Thms["Simplify"] = T(O("->"),TV("wff", -1),T(O("->"),TV("wff", -2),TV("wff", -1)));
GHT.Thms["Distribute"] = T(O("->"),T(O("->"),TV("wff", -1),T(O("->"),TV("wff", -2),TV("wff", -3))),T(O("->"),T(O("->"),TV("wff", -1),TV("wff", -2)),T(O("->"),TV("wff", -1),TV("wff", -3))));
GHT.ArrowScheme["mp"] = ["ax-mp", "ax-mp"]; //TODO: what does this second ax-mp really mean? why does that work?
GHT.ArrowScheme["->"] = ["_imim1", "_imim2"];
GHT.DisabledOptions.generify = 1;
GHT.DisabledOptions.equivalents = 1;
GHT.DisabledOptions.initials = 1;
GHT.DisabledOptions["term substitute"] = 1;
GHT.DisabledOptions.terminals = 1;
GHT.setProof((new GHT.ProofFactory()).newProof("Simplify"));

"""
            player.ghilbertInterfaces = ["PosPropCal"]
            player.ghilbertText = """
import (POSPROPCAL PosPropCal () "")
tvar (wff A B C D E F G H)
thm (_imim2 () () (-> (-> A B) (-> (-> C A) (-> C B)))
  (-> A B) C  Simplify
    C  A  B Distribute
      (-> (-> C (-> A B)) (-> (-> C A) (-> C B)))  (-> A B)  Simplify
    ax-mp
      (-> A B)  (-> C (-> A B))  (-> (-> C A) (-> C B)) Distribute
    ax-mp
  ax-mp
)
thm (_imim1 () () (-> (-> A B) (-> (-> B C) (-> A C)))
 (-> A B)  (-> B C)  Simplify
  B  C  A  _imim2
    (-> B C)  (-> A B)  (-> A C)  Distribute
  ax-mp
  (-> (-> B C) (-> A B))  (-> (-> B C) (-> A C))  (-> A B)  _imim2  ax-mp
 ax-mp
)
"""

            tip = '"Welcome!  I see you\'re new here.  Feel free to click around and explore.  You can\'t mess up."'
            player.put()
        self.response.out.write(player.setupJs);
        self.response.out.write('GHT.Tip.set("welcome", %s);\n' % tip);
        self.response.out.write(player.update_js());


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
tvar (wff A B C)
term (wff (-> A B))
stmt (Simplify () () (-> A (-> B A)))
stmt (Distribute () () (-> (-> A (-> B C)) (-> (-> A B) (-> A C))))
stmt (ax-mp () (A (-> A B)) B)
""",
                      'CorePropCal':"""
param (POSPROPCAL PosPropCal () "")
tvar (wff A B C)
term (wff (-. A))
stmt (Transpose () () (-> (-> (-. A) (-. B)) (-> B A)))
"""
                      }
        newProof = self.request.get('proof')
        thmName = self.request.get('thmName')
        proofText = player.ghilbertText + "\n" + newProof + "\n"
        output = StringIO.StringIO();
        output.write("Verifying: \n===\n%s\n===\n" % proofText);
        interfaces["-"] = proofText;
        urlctx = verify.DictionaryCtx(interfaces)
        ctx = verify.VerifyCtx(urlctx, verify.run, False)
        ctx.run(urlctx, '-', ctx, output)
        player.log += "\n# %s\n%s\n" % (strftime("%a, %d %b %Y %H:%M:%S +0000", gmtime()),
                                        self.request.get('log'))

        if ctx.error_count > 0:
            self.response.out.write("GHT.Tip.set('saveError', 'Cannot save!');\n/*\n%s\n*/" % output.getvalue())
            player.log += "\n# ERROR.\n" 
        else:
            player.ghilbertText = proofText;
            player.setupJs += "GHT.Thms['%s'] = %s;\n" % (thmName, self.request.get('source'))
            check_goal(player, newProof, thmName, self.response.out)
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
