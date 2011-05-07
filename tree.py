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
            goal.update_js = "GHT.Tip.lock('notUnlocked');\n"
            goal.new_location = "Outer Procal"

        if (name == "!unlock pred"):
            goal.new_ghilbert = """
# %s
import (PREDCAL PredCal (POSPROPCAL COREPROPCAL) "")
tvar (num a b c d e f g h)
var (num v w x y z v' w' x' y' z')
"""
            goal.new_js = """
// %s
// PredCal
GHT.Operators["A."] = new Operator("A.","\u2200","wff",["num","wff"],[NaN,1]);
GHT.ArrowScheme["A."] = [null, null];
GHT.EquivalenceScheme["A."] = [null, null];
GHT.Thms["alnfi"] = T(O("->"),TV("wff", -560),T(O("A."),TV("num", -120),TV("wff", -560)));
GHT.Thms["ax-4"] = T(O("->"),T(O("A."),TV("num", -120),TV("wff", -560)),TV("wff", -560));
GHT.Thms["ax-alim"] = T(O("->"),T(O("A."),TV("num", -120),T(O("->"),TV("wff", -560),TV("wff", -571))),T(O("->"),T(O("A."),TV("num", -120),TV("wff", -560)),T(O("A."),TV("num", -120),TV("wff", -571))));
GHT.Thms["ax-6"] = T(O("->"),T(O("-."),T(O("A."),TV("num", -120),TV("wff", -560))),T(O("A."),TV("num", -120),T(O("-."),T(O("A."),TV("num", -120),TV("wff", -560)))));
GHT.Thms["ax-7"] = T(O("->"),T(O("A."),TV("num", -120),T(O("A."),TV("num", -121),TV("wff", -560))),T(O("A."),TV("num", -121),T(O("A."),TV("num", -120),TV("wff", -560))));
GHT.Thms["ax-eqtr"] = T(O("->"),T(O("="),TV("num", -65),TV("num", -66)),T(O("->"),T(O("="),TV("num", -65),TV("num", -67)),T(O("="),TV("num", -66),TV("num", -67))));
GHT.Thms["ax-tyex"] = T(O("-."),T(O("A."),TV("num", -120),T(O("-."),T(O("="),TV("num", -120),TV("num", -65)))));

delete GHT.DisabledOptions.generify;

"""
            goal.update_js = "GHT.Tip.lock('predUnlocked');\n"
            goal.new_location = "Predcal"

        elif (name == "!con3"):
            goal.update_js = "GHT.Tip.lock('con3Unlocked');\n"
            goal.new_js ="""
// con3
GHT.Operators["-."].bindings[0] = -1;
GHT.ArrowScheme["-."][0] = "%s";
"""
        elif (name == "!unlock and"):
            goal.update_js = "GHT.Tip.lock('andUnlocked');\n"
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
            goal.update_js = "GHT.Tip.lock('anim1Unlocked');\n"
            goal.new_js = """
// anim1
GHT.Operators["/\\\\"].bindings[0] = 1;
GHT.ArrowScheme["/\\\\"][0] = "%s";
"""
        elif (name == "!anim2"):
            goal.update_js = "GHT.Tip.lock('anim2Unlocked');\n"
            goal.new_js = """
// anim2
GHT.Operators["/\\\\"].bindings[1] = 1;
GHT.ArrowScheme["/\\\\"][1] = "%s";
"""
        elif (name == "!unlock bi"):
            goal.update_js = "GHT.Tip.lock('biUnlocked');\n"
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
            goal.update_js = "GHT.Tip.lock('equivUnlocked');\n"
        elif (name == "!enable termsub"):
            goal.update_js = "GHT.Tip.lock('termsubUnlocked');\n"
            goal.new_js = """
// %s
delete GHT.DisabledOptions['term substitute'];
GHT.DisabledOptions.nodefthm = 1;
"""
        elif (name == "!orim1"):
            goal.new_js = """
// orim1
GHT.ArrowScheme["or"] = ["%s"];
"""
        elif (name == "!orbi1"):
            goal.update_js = "GHT.Tip.lock('orim1Unlocked');\n"
            goal.new_js = """
// orim1
GHT.Operators["or"].bindings[0] = 1;
GHT.EquivalenceScheme["or"] = ["%s"];
"""
        elif (name == "!orim2"):
            goal.new_js = """
// orim2
GHT.ArrowScheme["or"][1] = "%s";
"""
        elif (name == "!orbi2"):
            goal.update_js = "GHT.Tip.lock('orim2Unlocked');\n"
            goal.new_js = """
// orim2
GHT.Operators["or"].bindings[1] = 1;
GHT.EquivalenceScheme["or"][1] = "%s";
"""

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
    for i in range(len(goals) - 1):
        if player.goal == goals[i]:
            return goals[i+1]
    return goals[len(goals) - 1];

def check_goal(player, proof, thmName, stream):
    pattern = ".*thm \(.*" + player.goal.replace("\\","\\\\").replace("(","\(").replace(")","\)") + ".*"
    if re.match(pattern, proof):
        stream.write("\nGHT.Tip.goal();\n")
        player.score += 1
        player.goal = get_next_goal(player, stream)
        showTip = True;
        while (player.goal[0] == "!"):
            levelMatch = re.match("^!level (.*)", player.goal)
            if (levelMatch):
                player.level += 1;
                player.lastLevel = player.score;
                player.nextLevel = player.score + int(levelMatch.group(1))
                stream.write("\nGHT.levelUp();\n");
            else:
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
        stream.write("\nGHT.dismiss();\n");
        stream.write("\nGHT.redecorate();\n");
        stream.write(leaderboard_js(player))
        return True
    else:
        stream.write("GHT.Tip.set('saved'); // %s\n" % player.goal)
        stream.write("/*\n #### MATCH: " + pattern + " \n AGAINST: " + proof + "\n*/\n")
        return False

   
class Player(db.Model):
    name = db.StringProperty()
    lastSeen = db.DateTimeProperty(auto_now=True)
    score = db.IntegerProperty(default=0)
    level = db.IntegerProperty(default=1)
    lastLevel = db.IntegerProperty(default=0)
    nextLevel = db.IntegerProperty(default=12)
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
        for k in ("score", "location", "goal", "name", "level", "lastLevel", "nextLevel"):
            dict[k] = getattr(self,k);

        return "\nGHT.updateUi('player',%s);\n" % simplejson.dumps(dict)
        
class StatusJs(webapp.RequestHandler):
    def get(self, playerName):
        player = Player.get_or_insert(key_name=playerName)
        if (True or player.goalTrain is None): #XXX
            if (random.random() < 1.1):
                key = "test02"
                player.goalTrain = GoalTrain.get_or_insert(key)
                player.goalTrain.goals = [
                    #"!level 12",
                    "() () (rarr A (rarr B (rarr C (rarr D (rarr E D)))))",
                    "() () (rarr A (rarr B (rarr C B)))",
                    "() () (rarr (rarr A B) (rarr (rarr C A) (rarr C B)))" ,
                    "() () (rarr (rarr A B) (rarr (rarr B C) (rarr A C)))" ,
                    "() () (rarr (rarr (rarr A B) C) (rarr B C))" ,
                    "() () (rarr (rarr A (rarr B C)) (rarr B (rarr A C)))" ,
                    "() () (rarr (rarr A B) (rarr A A))",
                    "() () (rarr A (rarr B B))",
                    "() () (rarr A A)",
                    "() () (rarr A (rarr (rarr A B) B))" ,
                    "() () (rarr (rarr (rarr A A) B) B)" ,
                    "() () (rarr (rarr A (rarr A B)) (rarr A B))",
                    "!unlock not",
                    "!level 9",
                    "() () (rarr (not A) (rarr A B))",
                    "() () (rarr (not (not A)) A)",
                    "() () (rarr A (not (not A)))",
                    "() () (rarr (rarr A B) (rarr (not B) (not A)))",
                    "!con3",
                    "() () (rarr (not (rarr A B)) (not B))",
                    "() () (rarr (not (rarr A B)) A)",
                    "() () (rarr A (rarr (not B) (not (rarr A B))))",
                    "() () (rarr (rarr (not A) A) A)",
                    "() () (not (rarr (rarr A A) (not (rarr B B))))",
                    "!unlock and",
                    "!level 14",
                    "() () (rarr (and A B) (not (rarr A (not B))))",
                    "() () (rarr (not (rarr A (not B))) (and A B))",
                    "() () (rarr (rarr A B) (rarr (and A C) (and B C)))",
                    "!anim1",
                    "() () (rarr (rarr A B) (rarr (and C A) (and C B)))",
                    "!anim2",
                    "() () (rarr (and A B) A)",
                    "() () (rarr (and A B) B)",
                    "() () (rarr A (rarr B (and A B)))",
                    "() () (rarr A (and A A))",
                    "() () (rarr (and A B) (and B A))",
                    "() () (rarr (rarr A B) (rarr A (and A B)))",
                    "() () (rarr (rarr A (rarr B C)) (rarr (and A B) C))",
                    "() () (rarr (and A (rarr A B)) B)",
                    "() () (rarr (and A (rarr B C)) (rarr B (and A C)))",
                    "() () (rarr (and (rarr A B) (rarr C D)) (rarr (and A C) (and B D)))",
                    "() () (and (rarr A A) (rarr B B))",
                    "!unlock bi",
                    "!level 13",
                    "() () (rarr (iff A B) (and (rarr A B) (rarr B A)))",
                    "() () (rarr (and (rarr A B) (rarr B A)) (iff A B))",
                    "() () (rarr (iff A B) (rarr A B))",
                    "() () (rarr (iff A B) (rarr B A))",
                    "() () (rarr (iff A B) (iff (rarr B C) (rarr A C)))", "!imbi1",
                    "() () (rarr (iff A B) (iff (rarr C A) (rarr C B)))", "!imbi2",
                    "() () (rarr (iff A B) (iff (iff A C) (iff B C)))", "!bibi1",
                    "() () (rarr (iff A B) (iff (iff C A) (iff C B)))", "!bibi2",
                    "() () (rarr A (rarr (iff A B) B))", "!mpbi",
                    "() () (rarr A (rarr (iff B A) B))", "!mpbir",
                    "() () (rarr (iff A B) (iff (and A C) (and B C)))", "!anbi1",
                    "() () (rarr (iff A B) (iff (and C A) (and C B)))", "!anbi2",
                    "() () (rarr (iff A B) (iff (not B) (not A)))", "!notbi",
                    "!enable equivalents",
                    "!level 11",
                    "() () (iff (iff A B) (iff B A))",
                    "() () (iff A A)",
                    "() () (iff A (not (not A)))",
                    "() () (iff (rarr A B) (rarr (not B) (not A)))",
                    "() () (iff (and A B) (not (rarr A (not B))))",
                    "() () (iff (and A B) (and B A))",
                    "() () (iff A (and A A))",
                    "() () (iff (rarr A (rarr B C)) (rarr B (rarr A C)))",
                    "() () (iff (and (and A B) C) (and A (and B C)))",
                    "() () (iff (rarr A (rarr B C)) (rarr (and A B) C))",
                    "() () (iff (iff A B) (and (rarr A B) (rarr B A)))",
                    "!enable termsub",
                    "!level 8",
                    "() () (iff (or A B) (rarr (not A) B))",
                    "() () (rarr A (or B A))",
                    "() () (rarr A (or A B))",
                    "() () (rarr (rarr A B) (rarr (or A C) (or B C)))", "!orim1",
                    "() () (rarr (iff A B) (iff (or A C) (or B C)))", "!orbi1",
                    "() () (rarr (rarr A B) (rarr (or C A) (or C B)))", "!orim2",
                    "() () (rarr (iff A B) (iff (or C A) (or C B)))", "!orbi2",
                    "() () (iff (or A B) (or B A))",
                    "!unlock pred",
                    "!level 20",
                    "() () (iff (exists z A) (not (forall z (not A))))",
                    "() () (rarr A (exists z A))",
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
window.exports = {};
 GHT.loadLibrary('js/orcat_PosPropCal.js');
exports.startUi = true;
/*
exports.Init(theory, arrowScheme, proofFactory);
*/

"""
            player.ghilbertInterfaces = ["PosPropCal.ghi"]
            player.ghilbertText = ""
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
        newProof = self.request.get('proof')
        thmName = self.request.get('thmName')
        pipe = StringIO.StringIO()
        for line in open('orcat/PosPropCal_bootstrap.gh', 'r'):
            pipe.write(str(line))
        pipe.write(player.ghilbertText + "\n" + newProof + "\n");
        output = StringIO.StringIO();
        proofText = pipe.getvalue();
        output.write("Verifying: \n===\n%s\n===\n" % proofText);
        urlctx = verify.UrlCtx('','-', pipe)
        ctx = verify.VerifyCtx(urlctx, verify.run, False)
        ctx.run(urlctx, '-', ctx, output)
        player.log += "\n# %s\n%s\n" % (strftime("%a, %d %b %Y %H:%M:%S +0000", gmtime()),
                                        self.request.get('log'))

        if ctx.error_count > 0:
            self.response.out.write("GHT.Tip.set('saveError', 'Cannot save!');\n/*\n%s\n*/" % output.getvalue())
            player.log += "\n# ERROR\n\n"
        else:
            player.ghilbertText = proofText;
            player.setupJs += self.request.get('source')
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
