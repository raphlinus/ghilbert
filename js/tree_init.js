// Initializes the tree game.  Also handles login, saving, and the corresponding
// communication with the server.
var GHT;
if (!GHT) {
    GHT = {};
}
if (!window.console) {
    window.console = {
        log: function() {
        }
    };
}
// Cookie logic stolen from quirksmode.org.
GHT.Cookie = {
    set: function (name, value, days) {
        if (days) {
            var date = new Date;
            date.setTime(date.getTime() + days * 24 * 60 * 60 * 1000);
            var expires = "; expires=" + date.toGMTString();
        } else {
            var expires = "";
        }
        document.cookie = name + "=" + value + expires + "; path=/";
    },
    get: function (name) {
        var nameEQ = name + "=";
        var ca = document.cookie.split(";");
        for (var i = 0; i < ca.length; i++) {
            var c = ca[i];
            while (c.charAt(0) == " ") {
                c = c.substring(1, c.length);
            }
            if (c.indexOf(nameEQ) == 0) {
                return c.substring(nameEQ.length, c.length);
            }
        }
        return null;
    }
};
GHT.levelUp = function() {
    document.getElementById("player.score").style.width = "100%";
    var iframe = document.createElement('iframe');
    iframe.src = "http://gruntle.me";
    iframe.style.width = "80%";
    iframe.style.height = "600px";
    window.setTimeout(
        function() {
            GHT.Tip.theDiv.innerHTML += "<br/>Congratulations, you <strong>levelled up</strong>!  Look at this cute picture for 10 seconds!<br/>";
            GHT.Tip.theDiv.appendChild(iframe);
        }, 500);
    window.setTimeout(
        function() {
            GHT.Tip.theDiv.removeChild(iframe);
            GHT.Tip.theDiv.innerHTML += "Okay, okay, get back to work.";
        }, 10000);

    //GHT.dismiss.popup = iframe;
};
GHT.Tip = {
    goal: function() {
        var span = document.getElementById("achieved");
        span.style.display = "inline";
        window.setTimeout(
            function() {
                span.className = "animated";
            }, 0);
        window.setTimeout(
            function() {
                span.style.display = "none";
                span.className = "";
            }, 1200); /* HACK: this must be synced with tree.css */
    },
    lock: function(tipKey) {
        // this HACK gets uglier and uglier and uglier.
        window.setTimeout(function() {
                              var score = GHT.UiObjs.player.score;
                              GHT.Tip.tips["tutorial" + score] = GHT.Tip.tips[tipKey];
                              GHT.dismiss();
                          }, 0);
    },
    set: function(tipKey, tipValue) {
        if (tipValue) {
            this.tips[tipKey] = tipValue;
        }
        if (this.tips[tipKey]) {
            this.theDiv.innerHTML = this.tips[tipKey];
            this.theDiv.style.visibility = "visible";
            this.currentTip = tipKey;
        }
    },
    clear: function(tipKey) {
        if (this.currentTip && (!tipKey || this.currentTip === tipKey)) {
            this.theDiv.style.visibility = "hidden";
            delete this.currentTip;
        }
    },
    tips: {
        login: "Welcome, anonymous guest!  Please enter a nickname so we can save your progress."
        ,saved: "Saved."
        ,returned: "Welcome back.  We missed you! (Press ESCAPE to close.)"
        ,naming:'Tip: Choosing more descriptive names for the terminals you save will help you find them later when you need to use them.'
        ,arrow:'Tip: The diagram <div><span class="tree wrapper arg"><span class="tree operator type_wff binding_initial">&#x2192;<\/span><span class="tree args"><span class="tree var type_wff binding_terminal first arg">A<\/span><span class="tree var type_wff binding_initial arg">B<\/span><\/span><\/span><\/div><br style="clear:both"/> is written "(&#x2192; A B)" and pronounced "A arrows B."'
        ,color:'Tip: A <span style="border-top:2px solid red">red<\/span> subdiagram can be replaced by anything it is known to arrow.  A <span style="border-top:2px solid blue">blue<\/span> subdiagram can be replaced by anything known to arrow it.'
        ,bindings:'Tip: The operator <span class="operator">&#x2192;<\/span> bequeaths its same color to its right child, and the opposite color to its left child.'
        ,escape:"Tip: The Escape key closes any menu that's in your your way."
        ,notUnlocked:"You've discovered a new location!<br/>As you arrive in Outer Procal, you pick up a new operator, <span class='operator'>&#x00ac;<\/span>) , and a new terminal, Transpose."
        ,con3Unlocked:"Operator <span class='operator'>&#x00ac;<\/span> now passes on the opposite of its color to its only child."
        ,andUnlocked:"A plot point occurs, and you acquire a new operator <span class='operator'>&#x2227;<\/span> and its terminal Conjoin."
        ,anim1Unlocked:"Operator <span class='operator'>&#x2227;<\/span> now passes on its color to its left child!"
        ,anim2Unlocked:"Operator <span class='operator'>&#x2227;<\/span> now passes on its color to its right child too!"
        ,orim1Unlocked:"Operator <span class='operator'>or<\/span> now passes on its color to its left child!"
        ,orim2Unlocked:"Operator <span class='operator'>or<\/span> now passes on its color to its right child too!"
        ,biUnlocked:"A new operator appears! Your new terminal Equivalate just says that <span class='operator'>&#x2194;<\/span> is like <span class='operator'>&#x2192;<\/span> going in both directions."
        ,equivUnlocked:"Operator <span class='operator'>&#x2194;<\/span> now passes a <span style='border-top:2px solid purple'>purple<\/span> status to its children, which can only be equivalated."
        ,termsubUnlocked:"Term Substitute unlocked.  You can use this to make definitions... if you can figure out how!"
        ,newPlayer: "Welcome to the playtest!  Please excuse the shoddy graphics and lack of a storyline.  Those will come later.  Right now I just want to see if you can solve the puzzles.  Press ESCAPE on your keyboard to begin."
        ,tutorial0: "You start with two terminals: Simplify, and Distribute.  Let's see how Simplify works.  Click on the Roof (that's the topmost arrow below), then click Simplify.  Repeat two more times times so your diagram matches the Goal, then Save it."
        ,tutorial1: "Great!  It doesn't matter which letter goes with which number, as long as you have the same pattern.  You've already already seen this next goal, so just hit your browser's BACK button twice to return to it.  (BACK/FORWARD lets you undo/redo anytime.  Scrubbing between two diagrams can help show how they relate.)"
        ,tutorial2: "Nice.  You may wonder why it's called <em>Simplify<\/em> when so far it's only added complexity, but terminals work backwards on blue spots.  To see this (and get another goal), <span class='startwith'>start over with<\/span> Distribute and then use Simplify on its blue left side."
        ,tutorial3: "Rockin'.  Now let's take Distribute out for a spin. Use it on the Roof right now, then Simplify the left side again.  (Incidentally, it's called <em>Distribute<\/em> because of the way that 2 &times; (3 + 4) = 2 &times; 3 + 2 &times; 4.  Can you see the similarity?)"
        ,tutorial4: "Sweet!  You can apply any terminal you previously saved (either to get a goal or because it looked handy).  Try it out: <span class='startwith'>start over with<\/span> Simplify, then apply the terminal you just saved to the Roof."
        ,tutorial5: "Splendid.  Each terminal transforms part of the diagram in a different way.  Try to develop an intuition for how they all work.  (The previews hint at what will happen; or just try stuff and then Undo.) "
        ,tutorial6: "You're getting the hang of it now!"
        ,tutorial7: "Don't stop now; if you can get a few more, you'll level up..."
        ,tutorial9: "This one requires a tricky process called <em>unification<\/em>.  A terminal may not seem applicable, but you can still use it if replacing a letter with a new subdiagram would make it work."
    },
    randomTips: ["naming", "arrow", "color", "bindings", "escape"],
    randomTipIndex: 0,
    showRandom: function() {
        var score = GHT.UiObjs.player.score;
        if (this.tips["tutorial" + score]) {
            this.set("tutorial" + score);
        } else if (Math.random() < .1) {
            this.set(this.randomTips[this.randomTipIndex++ % this.randomTips.length]);
        } else {
            this.clear();
        }
    },
    theDiv: document.getElementById("tip")
};
GHT.UiObjs = {};
GHT.updateUi = function(nodeBase, obj) {
    GHT.UiObjs[nodeBase] = obj;
    for (var k in obj) {
        var nodeName = nodeBase + "." + k;
        var node = document.getElementById(nodeName);
        var val = obj[k];
        if (k === "XXXgoal") { // HACK
            val = val.substring(6);
            GHT.theGoal = val;
            val = GHT.termFromSexp(val);
            GHT.theGoalString = val.toString(GHT.makeVarMapper({}, GHT.goalVarNames));
            val = GHT.makeTable(false, val, [], 1,
                                GHT.makeVarMapper({}, GHT.goalVarNames));
            while (node.firstChild) node.removeChild(node.firstChild);
            node.appendChild(val);
        } else if (node) {
            if (node.type === "text"){
                node.value = val;
            } else {
                node.innerHTML = val;
            }
        }
    }
    if (nodeBase == "player") { // TODO: clean this up.
        var scoreWidth = 100 * (obj.score - obj.lastLevel) / (obj.nextLevel - obj.lastLevel);
        scoreWidth = (scoreWidth === 0) ? "" : scoreWidth + "%";
        document.getElementById("player.score").style.width = scoreWidth;
    }
};

// Startup: set the playerName, get the latest stuff
(function() {
     var playerNameCookie = "player.name";
     var playerNameField = document.getElementById("player.name");
     var timeoutId;
     playerNameField.onkeyup = function() {
         window.clearTimeout(timeoutId);
         timeoutId = window.setTimeout(playerNameField.onchange, 500);
     };
     playerNameField.onchange = function() {
         var playerName = playerNameField.value;
         if (playerName !== GHT.playerName) {
             GHT.playerName = playerName;
             GHT.Cookie.set(playerNameCookie, GHT.playerName);
             GHT.Tip.clear("login");
             var xhr = new XMLHttpRequest();
             xhr.onreadystatechange = function () {
                 if (xhr.readyState === 4) {
                     eval(xhr.responseText);
                 } else if (xhr.readyState > 4) {
                     console.log("login xhr: " + xhr.readyState);
                 }
             };
             xhr.open("GET", "/tree/status/" + encodeURIComponent(GHT.playerName), true);
             xhr.send(null);
         }
     };
     var playerName = GHT.Cookie.get(playerNameCookie);
     if (!playerName) {
         GHT.Tip.set("login");
     } else {
         playerNameField.value = playerName;
         playerNameField.onchange();
     }
     function makeSavePacket(isDefThm) {
         var packet = {};
         packet.playerName = encodeURIComponent(GHT.playerName);
         packet.thmName = document.getElementById("theorem.name").value;
         var term;
         if (isDefThm) {
             var defthm = GHT.getProof().defthm(packet.thmName);

             packet.thmName  = "df-" + packet.thmName;
             term = defthm[0];
             packet.proof = defthm[1];
             packet.source = defthm[2] +
                 "\nGHT.Thms['" + packet.thmName + "'] = " + term.toSource() + ";\n";
         } else {
             term = GHT.theTerm;
             packet.proof = GHT.getProof().getProof(packet.thmName);
             packet.source = "GHT.Thms['" + packet.thmName + "'] = " + term.toSource() + ";\n";
         }
         GHT.Thms[packet.thmName] = term.clone();
         GHT.redecorate();
         packet.log = "";
         var vers = GHT.getVersion();
         for (var i = GHT.theFirstStep; i <= vers; i++){
             packet.log += GHT.undoStack[i].step + "\n";
         }
         packet.log += "GHT.SaveAs('" + packet.thmName + "'); // "
             + packet.source + "\n";
         console.log(packet.log);
         return packet;
     }
     function submitForm(event, isDefThm) {
         var packet = makeSavePacket(isDefThm);
         var xhr = new XMLHttpRequest();
         xhr.onreadystatechange = function () {
             if (xhr.readyState === 4) {
                 eval(xhr.responseText);
             } else if (xhr.readyState > 4) {
                 console.log("save xhr: " + xhr.readyState);
             }
             document.getElementById("theorem.name").value = "";
         };
         xhr.open("POST", "/tree/save", true);
         xhr.setRequestHeader('Content-Type', 'application/x-www-form-urlencoded');
         var packetStr = "";
         for (var key in packet) {
             if (packetStr) {
                 packetStr += "&";
             }
             packetStr += encodeURIComponent(key) + "=" + encodeURIComponent(packet[key]);
         }
         xhr.send(packetStr);
     };
     document.getElementById("save").onclick = submitForm;
     document.getElementById("theorem.name").onkeyup = function(e) {
         if (e.keyCode == 13) { // Enter
             submitForm();
             return false;
         }
         return true;
     };
     document.onkeyup = function(e) {
         if (e.keyCode == 27) { // ESC
             GHT.dismiss();
             return false;
         }
         return true;
     };
     GHT.SaveAs = function(name) {
         document.getElementById("theorem.name").value = name;
         submitForm();
     };
     GHT.DefThm = function(name) {
         if (name) document.getElementById("theorem.name").value = name;
         GHT.dismiss();
         submitForm(null, true);
     };
     document.getElementById("defthm").onclick = function() { GHT.DefThm();};

     GHT.loadLibrary = function(src) {
	 var head= document.getElementsByTagName('head')[0];
	 var script= document.createElement('script');
	 script.type= 'text/javascript';
	 script.src = src;
	 head.appendChild(script);
     };
 })();

GHT.Operators = {};
GHT.Thms = {};
GHT.DisabledOptions = {};

/*
 // Deductions used to propagate an arrowing up the tree.
 // ArrowScheme[op][n] should be an arrow from "x arrow
 // y" to "op(..x..) arrow op(..y..)".  The direction of the arrow
 // may get be reversed if the op.binding[n] is -1.
 // TODO: HACK: Also, each scheme must have an 'mp' property mapping to the
 // appropriate modus-ponens inference.
 GHT.ArrowScheme = {  // TODO: autodetect these
 "mp": ["ax-mp", "ax-mp"], //TODO: what does this second ax-mp really mean? why does that work?
 "-.": ["con3i"],
 "->": ["imim1i", "imim2i"],
 "/\\":["anim1i", "anim2i"],
 //TODO(pickup): this one isn't right... or ever needed??
 "<->":["imbi1i", "imbi2i"],
 "=":  ["eqeq1", "eqeq2"],
 "E.": ["exalpha", "19.22i"],
 "A.": ["alpha", "19.20i"]
 //,
 };

 GHT.EquivalenceScheme = {
 "mp": ["mpbi", "mpbir"],
 "/\\":["anbi1i", "anbi2i"],
 "->": ["imbi1i", "imbi2i"],
 "<->":["bibi1i", "bibi2i"],
 "e.": ["eleq1i", "eleq2i"],
 "E!": ["eualpha", "eubii"],
 "A.": ["alpha", "albii"],
 "=":  ["eqeq1", "eqeq2"],
 "-.": ["notbii"],
 "E.": ["exalpha", "exbid"] //TODO:HACK
 };
 GHT.EquivalenceThms = {
 "num": {refl: "eqid", tr: "TODO:eqtr", sym: "TODO:eqsym"},
 "set": {refl: "seqid", tr: "TODO:seqtr", sym: "TODO:seqsym"},
 "wff": {refl: "biid", tr: "TODO:bitr", sym: "TODO:bisym"}
 };
 // Inferences used to assert the terminality of a terminal
 GHT.Terminators = {
 "wff": "a1i"
 };
 */
GHT.ArrowScheme = {};
GHT.EquivalenceScheme = {};
GHT.EquivalenceThms = {};
GHT.Terminators = {};
