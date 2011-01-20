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
    set: function(tipKey) {
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
    }
};
GHT.Tip.theDiv = document.getElementById("tip");

// Startup: set the playerName, get the latest stuff
(function() {
    var playerNameCookie = "playerName";
    var playerNameField = document.getElementById("playerName");
    var playerName = GHT.Cookie.get(playerNameCookie);
    var timeoutId;
    playerNameField.onkeyup = function() {
        window.clearTimeout(timeoutId);
        timeoutId = window.setTimeout(playerNameField.onchange, 500);
    };
    playerNameField.onchange = function() {
        playerName = playerNameField.value
        GHT.Cookie.set(playerNameCookie, playerName);
        GHT.Tip.clear("login");
        var xhr = new XMLHttpRequest();
        xhr.onreadystatechange = function () {
            if (xhr.readyState === 4) {
                var status = eval(xhr.responseText);
                document.getElementById("playerScore").innerHTML = status.score;
                document.getElementById("playerLocation").innerHTML = status.location;
                document.getElementById("goal").innerHTML = status.goal;
            } else {
                console.log("login xhr: " + xhr.readyState);
            }
        };
        xhr.open("GET", "/tree/status/" + encodeURIComponent(playerName), true);
        xhr.send(null);
    };
    if (!playerName) {
        GHT.Tip.set("login");
    } else {
        playerNameField.value = playerName;
        playerNameField.onchange();
    }
})();
