// Initializes the tree game.  Also handles login, saving, and the corresponding
// communication with the server.
var GHT;
if (!GHT) {
    GHT = {};
}
if (!console) {
    console = {
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
GHT.Tip = {
    set: function(tipKey, tipValue) {
        if (tipValue) {
            this.tips[tipKey] = tipValue;
        }
        this.theDiv.innerHTML = this.tips[tipKey];
        this.theDiv.style.display = "block";
        this.currentTip = tipKey;
    },
    clear: function(tipKey) {
        if (!tipKey || this.currentTip === tipKey) {
            this.theDiv.style.display = "none";
            delete this.currentTip;
        }  
    },
    tips: {
        login: "Welcome, anonymous guest!  Please enter a nickname so we can save your progress."
        ,saved: "Saved."
        ,achieved: "Goal Achived!"
        ,arrow:'Tip: The tree <table class="type_wff binding_terminal" style="display:inline"><tr><td colspan="2" class="operator">&#x2192;<\/td><\/tr><tr><td><span class="var type_wff binding_terminal">A<\/span><\/td><td><span class="var type_wff binding_initial">B<\/span><\/td><\/tr><\/table> is written "(&#x2192; A B)" and pronounced "A arrows B."'
        ,color:'Tip: A <span style="border-top:2px solid red">red<\/span> subtree can be replaced by anything it is known to arrow.  A <span style="border-top:2px solid blue">blue<\/span> subtree can be replaced by anything known to arrow it.'
        ,letters:'Tip: After each step, all letters are remapped back to the beginning of the alphabet.'
        ,bindings:'Tip: The operator <span class="operator">&#x2192;<\/span> bequeaths its same color to its right child, and the opposite color to its left child.'
        ,negUnlocked:"Goal Achieved!<br/>You've discovered a new location!<br/>As you arrive in Outer Procal, you pick up a new operator (<span class='operator'>&#x00ac;<\/span>) and a new terminal (Transpose)."
        ,andUnlocked:"Goal Achieved!<br/>A plot point occurs, and you acquire a new operator (<span class='operator'>&#x2227;<\/span>) and its terminal (Conjoin)."
        ,anim1Unlocked:"Goal Achieved!<br/>Operator <span class='operator'>&#x2227<\/span>; now passes on binding to its left child!"
        ,anim2Unlocked:"Goal Achieved!<br/>Operator <span class='operator'>&#x2227<\/span>; now passes on binding to its right child too!"
        ,biUnlocked:"Goal Achieved!<br/>A new operator appears! Your new terminal Equivalate just says that <span class='operator'>&#x2194;<\/span> is like <span class='operator'>&#x2192;<\/span> going in both directions."
    },
    theDiv: document.getElementById("tip")
};
GHT.updateUi = function(nodeBase, obj) {
    for (var k in obj) {
        var nodeName = nodeBase + "." + k;
        var node = document.getElementById(nodeName);
        if (node) {
            if (node.type === "text"){
                node.value = obj[k];
            } else {
                node.innerHTML = obj[k];
            }
        } else {
            console.log("Node not found: " + nodeName);
        }
    }
};

// Startup: set the playerName, get the latest stuff
(function() {
     var playerNameCookie = "player.name";
     var playerNameField = document.getElementById("player.name");
     GHT.playerName = GHT.Cookie.get(playerNameCookie);
     var timeoutId;
     playerNameField.onkeyup = function() {
         window.clearTimeout(timeoutId);
         timeoutId = window.setTimeout(playerNameField.onchange, 500);
     };
     playerNameField.onchange = function() {
         GHT.playerName = playerNameField.value;
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
     };
     if (!GHT.playerName) {
         GHT.Tip.set("login");
     } else {
         playerNameField.value = GHT.playerName;
         playerNameField.onchange();
     }
     function submitForm() {
         var packet = {};
         packet.playerName = encodeURIComponent(GHT.playerName);
         packet.thmName = document.getElementById("theorem.name").value;
         GHT.Thms[packet.thmName] = GHT.theTerm.clone();
         GHT.redecorate();
         packet.log = "";
         var vers = GHT.getVersion();
         for (var i = 1; i <= vers; i++){
             packet.log += GHT.undoStack[i].step + "\n";
         }
         packet.source = GHT.theTerm.toSource();
         packet.log += "#### Save as " + name + " : " + packet.source + "\n";
         console.log(packet.log);
         packet.proof = GHT.getProof().getProof(packet.thmName);
         var xhr = new XMLHttpRequest();
         xhr.onreadystatechange = function () {
             if (xhr.readyState === 4) {
                 eval(xhr.responseText);
             } else if (xhr.readyState > 4) {
                 console.log("save xhr: " + xhr.readyState);
             }
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

 })();

GHT.Operators = {};
GHT.Thms = {};
GHT.DisabledOptions = {};

/*
 // Inferences used to propagate an arrowing up the tree.
 // Inferences[op][n] should be an inference that transforms "x arrow
 // y" into "op(..x..) arrow op(..y..)".  The direction of the arrow
 // may get be reversed if the op.binding[n] is -1.
 // TODO: HACK: Also, each scheme must have an 'mp' property mapping to the
 // appropriate modus-ponens inference.
 GHT.ArrowScheme = {  // TODO: autodetect these
 "mp": ["ax-mp", "ax-mp"], //TODO: what does this second ax-mp really mean? why does that work?
 "-.": ["con3i"],
 "->": ["imim1i", "imim2i"],
 "/\\": ["anim1i", "anim2i"],
 //TODO(pickup): this one isn't right... or ever needed??
 "<->": ["imbi1i", "imbi2i"],
 "=": ["eqeq1", "eqeq2"],
 "E.": ["exalpha", "19.22i"],
 "A.": ["alpha", "19.20i"]
 //,
 };

 GHT.EquivalenceScheme = {
 "mp": ["mpbi", "mpbir"],
 "/\\": ["anbi1i", "anbi2i"],
 "->": ["imbi1i", "imbi2i"],
 "<->": ["bibi1i", "bibi2i"],
 "e.": ["eleq1i", "eleq2i"],
 "E!": ["eualpha", "eubii"],
 "A.": ["alpha", "albii"],
 "=": ["eqeq1", "eqeq2"],
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
