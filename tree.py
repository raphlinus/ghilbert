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
import random

from google.appengine.api import users
from google.appengine.ext import webapp
from google.appengine.ext.webapp.util import run_wsgi_app
from google.appengine.ext import db

from django.utils import simplejson

class GoalTrain(db.Model):
    name = db.StringProperty()
    # Each element in the list is a ghilbert expression for the next goal in the chain.
    # It can also be "!special", in which case we'll execute the appropriate "special" goal,
    # feeding in the name of the last-saved theorem.
    goals = db.StringListProperty()

# for special goals
class Goal(db.Model):
    name = db.StringProperty()
    score = db.IntegerProperty(default=0)
    # Location to move the player to after this goal.
    new_location = db.StringProperty()
    # This text will be appended to the player's ghilbert_text when the theorem is unlocked.
    # Must have one %s which will be replaced by the player's chosen theorem name.
    new_ghilbert = db.TextProperty()
    # Like new_ghilbert, this will be added to the player's setup_js.  It will also be dumped
    # into the response for immediate eval.
    new_js = db.TextProperty()
    # One-time js to be sent only when the goal is achieved.  If none, put up the default tip. 
    update_js = db.TextProperty()
    # TODO: which interfaces are required; which goals are required; branch points

def leaderboard_js(player):
    q = Player.all()
    q.filter("score !=", 0)
    q.order("-score")
    results = q.fetch(15)
    html = ""
    for p in results:
        if p.name == player.name:
            html += "<b>%s: %d</b> " % (p.name, p.score)
        else:
            html += "%s: %d " % (p.name, p.score)
    html = html.replace('"','')
    return "document.getElementById('leaderboard').innerHTML='%s';\n" % html
#TODO:hack
def get_goal(name):
    goal = Goal.get_or_insert(key_name=name)
    if (True): #goal.name is None
        goal.name = name
        if (name == "!unlock not"):
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
            goal.new_location = "Outer Procal"

        elif (name == "!con3"):
            goal.update_js = "GHT.Tip.set('con3Unlocked');\n"
            goal.new_js ="""
// con3
GHT.Operators["-."].bindings[0] = -1;
GHT.ArrowScheme["-."][0] = "%s";
"""
        elif (name == "!unlock and"):
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
        elif (name == "!anim1"):
            goal.update_js = "GHT.Tip.set('anim1Unlocked');\n"
            goal.new_js = """
// anim1
GHT.Operators["/\\\\"].bindings[0] = 1;
GHT.ArrowScheme["/\\\\"][0] = "%s";
"""
        elif (name == "!anim2"):
            goal.update_js = "GHT.Tip.set('anim2Unlocked');\n"
            goal.new_js = """
// anim2
GHT.Operators["/\\\\"].bindings[1] = 1;
GHT.ArrowScheme["/\\\\"][1] = "%s";
"""
        elif (name == "!unlock bi"):
            goal.update_js = "GHT.Tip.set('biUnlocked');\n"
            goal.new_js = """
// %s
// Bi
GHT.Operators["<->"] = new Operator("<->","\u2194","wff",["wff","wff"],[Infinity,Infinity])
GHT.Thms["Equivalate"] =  T(O("/\\\\"),T(O("->"),T(O("<->"),TV("wff", -1),TV("wff", -2)),T(O("/\\\\"),T(O("->"),TV("wff", -1),TV("wff", -2)),T(O("->"),TV("wff", -2),TV("wff", -1)))),T(O("->"),T(O("/\\\\"),T(O("->"),TV("wff", -1),TV("wff", -2)),T(O("->"),TV("wff", -2),TV("wff", -1))),T(O("<->"),TV("wff", -1),TV("wff", -2))));
GHT.ArrowScheme["<->"] = [null, null];
GHT.EquivalenceScheme = {};
GHT.EquivalenceScheme["->"] = [null, null];
GHT.EquivalenceScheme["<->"] = [null, null];
GHT.EquivalenceScheme["mp"] = [null, null];
GHT.EquivalenceScheme["/\\\\"] = [null, null];
"""
            goal.new_ghilbert = """
defthm (Equivalate wff (<-> A B) () ()
     (/\ (-> (<-> A B) (/\ (-> A B) (-> B A)))
         (-> (/\ (-> A B) (-> B A)) (<-> A B)))
    (/\ (-> A B) (-> B A))  (/\ (-> A B) (-> B A))  %s
)
"""
        elif (name == "!imbi1"):
            goal.new_js = '\n GHT.EquivalenceScheme["->"][0] = "%s"; \n'
        elif (name == "!imbi2"):
            goal.new_js = '\n GHT.EquivalenceScheme["->"][1] = "%s"; \n'
        elif (name == "!bibi1"):
            goal.new_js = '\n GHT.EquivalenceScheme["<->"][0] = "%s"; \n'
        elif (name == "!bibi2"):
            goal.new_js = '\n GHT.EquivalenceScheme["<->"][1] = "%s"; \n'
        elif (name == "!mpbi"):
            goal.new_js = '\n GHT.EquivalenceScheme["mp"][0] = "_mpbi";//%s \n'
            #TODO: deductionify (deduce?) these from the inferences
            goal.new_ghilbert = """
thm (_mpbi () (1 A 2 (<-> A B)) B
2  1  A  B  %s   ax-mp    ax-mp)
"""
        elif (name == "!mpbir"):
            goal.new_js = '\n GHT.EquivalenceScheme["mp"][1] = "_mpbir";//%s \n'
            goal.new_ghilbert = """
thm (_mpbir () (1 A 2 (<-> B A)) B
2  1  A  B  %s   ax-mp    ax-mp)
"""
        elif (name == "!anbi1"):
            goal.new_js = '\n GHT.EquivalenceScheme["/\\\\"][0] = "%s"; \n'
            goal.next = "anbi2"
            goal.ghilbert = "() () (-> (<-> A B) (<-> (/\ A C) (/\ B C)))"
        elif (name == "!anbi2"):
            goal.new_js = """
GHT.EquivalenceScheme["/\\\\"][1] = "%s";
"""
        elif (name == "!notbi"):
            goal.new_js = """
GHT.EquivalenceScheme["-."] = ["%s"];
"""
        elif (name == "!enable equivalents"):
            goal.new_js = """
// %s
GHT.Operators["<->"].bindings = [0, 0];
delete GHT.DisabledOptions.equivalents;
"""
            goal.update_js = "GHT.Tip.set('equivUnlocked');\n"

        else:
            goal.html = "Sorry, goal '%s' isn't defined yet.  No one thought you'd make it this far!" % name
            return goal
    # TODO: real parser / html formatter
    goal.value = 1
    goal.put()
    return goal
#TODO: OO

def get_next_goal(player, stream):
    goals = player.goalTrain.goals
    for i in range(len(goals)):
        if player.goal == goals[i]:
            return goals[i+1]
    return "UNKNOWN"

def check_goal(player, proof, thmName, stream):
    pattern = "thm \([^)]* " + player.goal.replace("\\","\\\\").replace("(","\(").replace(")","\)")
    if re.match(pattern, proof):
        player.score += 1
        stream.write("GHT.Tip.set('achieved');")
        player.goal = get_next_goal(player, stream)
        while (player.goal[0] == "!"):
            goal = get_goal(player.goal)
            if (goal.new_js):
                player.setupJs += goal.new_js % thmName
                stream.write(goal.new_js % thmName);
            if (goal.new_ghilbert):
                player.ghilbertText += goal.new_ghilbert % thmName
            if (goal.update_js):
                stream.write(goal.update_js)
            if (goal.new_location):
                player.location = goal.new_location
            stream.write("// %s" % player.goal)
            player.goal = get_next_goal(player, stream)
        player.put()
        stream.write(player.update_js())
        stream.write(leaderboard_js(player))
        stream.write("\nGHT.redecorate();\n");
        return True
    else:
        stream.write("GHT.Tip.set('saved'); // %s\n" % player.goal)
        stream.write("/*\n MATCH: " + pattern + " #### AGAINST: " + proof + "\n*/\n")
        return False

   
class Player(db.Model):
    name = db.StringProperty()
    lastSeen = db.DateTimeProperty(auto_now=True)
    score = db.IntegerProperty(default=0)
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
    # Which Goal Train is this user on?
    goalTrain = db.ReferenceProperty(GoalTrain)
    # Javascript for updating the UI to reflect this object's current state
    def update_js(self):
        dict = {};
        for k in ("score", "location", "goal", "name"):
            dict[k] = getattr(self,k);

        return "\nGHT.updateUi('player',%s);\n" % simplejson.dumps(dict)
        
class StatusJs(webapp.RequestHandler):
    def get(self, playerName):
        player = Player.get_or_insert(key_name=playerName)
        if (player.goalTrain is None):
            if (random.random() < 1.1):
                key = "test02"
                player.goalTrain = GoalTrain.get_or_insert(key)
                player.goalTrain.goals = [
                    "() () (-> A (-> B (-> C (-> D (-> E D)))))",
                    "() () (-> A (-> B (-> C B)))",
                    "() () (-> (-> A B) (-> (-> C A) (-> C B)))" ,
                    "() () (-> (-> A B) (-> (-> B C) (-> A C)))" ,
                    "() () (-> (-> (-> A B) C) (-> B C))" ,
                    "() () (-> (-> A B) (-> A A))",
                    "() () (-> A (-> B B))",
                    "() () (-> A A)",
                    "() () (-> A (-> (-> A B) B))" ,
                    "() () (-> (-> (-> A A) B) B)" ,
                    "() () (-> (-> A (-> B C)) (-> B (-> A C)))" ,
                    "() () (-> (-> A (-> A B)) (-> A B))",
                    "!unlock not",
                    "() () (-> (-. A) (-> A B))",
                    "() () (-> A (-. (-. A)))",
                    "() () (-> (-. (-. A)) A)",
                    "() () (-> (-> A B) (-> (-. B) (-. A)))",
                    "!con3",
                    "() () (-> (-. (-> A B)) A)",
                    "() () (-> A (-> (-. B) (-. (-> A B))))",
                    "() () (-> (-> (-. A) A) A)",
                    "() () (-. (-> (-> A A) (-. (-> B B))))",
                    "!unlock and",
                    "() () (-> (/\ A B) (-. (-> A (-. B))))",
                    "() () (-> (-. (-> A (-. B))) (/\ A B))",
                    "() () (-> (-> A B) (-> (/\ A C) (/\ B C)))",
                    "!anim1",
                    "() () (-> (-> A B) (-> (/\ C A) (/\ C B)))",
                    "!anim2",
                    "() () (-> (/\ A B) A)",
                    "() () (-> (/\ A B) B)",
                    "() () (-> A (-> B (/\ A B)))",
                    "() () (-> A (/\ A A))",
                    "() () (-> (/\ A B) (/\ B A))",
                    "() () (-> (-> A B) (-> A (/\ A B)))",
                    "() () (-> (-> A (-> B C)) (-> (/\ A B) C))",
                    "() () (-> (/\ A (-> A B)) B)",
                    "() () (-> (/\ A (-> B C)) (-> B (/\ A C)))",
                    "() () (-> (/\ (-> A B) (-> C D)) (-> (/\ A C) (/\ B D)))",
                    "() () (/\ (-> A A) (-> B B))",
                    "!unlock bi",
                    "() () (-> (<-> A B) (/\ (-> A B) (-> B A)))",
                    "() () (-> (/\ (-> A B) (-> B A)) (<-> A B))",
                    "() () (-> (<-> A B) (-> A B))",
                    "() () (-> (<-> A B) (-> B A))",
                    "() () (-> (<-> A B) (<-> (-> A C) (-> B C)))", "!imbi1",
                    "() () (-> (<-> A B) (<-> (-> C A) (-> C B)))", "!imbi2",
                    "() () (-> (<-> A B) (<-> (<-> A C) (<-> B C)))", "!bibi1",
                    "() () (-> (<-> A B) (<-> (<-> C A) (<-> C B)))", "!bibi2",
                    "() () (-> A (-> (<-> A B) B))", "!mpbi",
                    "() () (-> A (-> (<-> B A) B))", "!mpbir",
                    "() () (-> (<-> A B) (<-> (/\ A C) (/\ B C)))", "!anbi",
                    "() () (-> (<-> A B) (<-> (/\ C A) (/\ C B)))", "!anbi2",
                    "() () (-> (<-> A B) (<-> (-. B) (-. A)))", "!notbi",
                    "!enable equivalents",
                    "() () (<-> (<-> A B) (<-> B A))",
                    "() () (<-> A A)",
                    "() () (<-> A (-. (-. A)))",
                    "() () (<-> (-> A B) (-> (-. B) (-. A)))",
                    "() () (<-> (/\ A B) (-. (-> A (-. B))))",
                    "() () (<-> (/\ A B) (/\ B A))",
                    "() () (<-> A (/\ A A))",
                    "() () (<-> (-> A (-> B C)) (-> B (-> A C)))",
                    "() () (<-> (/\ (/\ A B) C) (/\ A (/\ B C)))",
                    "() () (<-> (-> A (-> B C)) (-> (/\ A B) C))",
                    "() () (<-> (<-> A B) (/\ (-> A B) (-> B A)))",

                    "TODO"
                    ]
                player.goalTrain.put()
        tip = '"returned"';
        if (player.location is None):
            player.score = 0
            player.location = "Inner Procal"
            player.goal=player.goalTrain.goals[0]
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

            tip = '"newPlayer"'
            player.put()
        self.response.out.write(player.setupJs);
        self.response.out.write('GHT.Tip.set(%s);\n' % tip);
        self.response.out.write(player.update_js());
        self.response.out.write(leaderboard_js(player))

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
            player.log += "\n# ERROR\n\n"
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
