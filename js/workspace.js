// Copyright 2012 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

var Range = ace.require('ace/range').Range;
var EditSession = ace.require('ace/edit_session').EditSession;

function Tab(workspace, tabmenuelement, contentid) {
    this.workspace = workspace;
    this.tabmenuelement = tabmenuelement;
    this.contentid = contentid;
}

Tab.prototype.show = function() {
    document.getElementById(this.contentid).style.display = "block";
    if (this.session) {
        document.getElementById("editor").style.display = "block";
        this.workspace.editor.setSession(this.session);
        this.workspace.editor.resize();
        this.workspace.editor.focus();
    }
    this.tabmenuelement.className = "active";
}

Tab.prototype.hide = function() {
    document.getElementById(this.contentid).style.display = "none";
     if (this.session) {
        document.getElementById("editor").style.display = "none";
    }
   this.tabmenuelement.className = "";
}

function Workspace() {
    this.tabs = [];
    this.currenttab = null;
    this.tabcounter = 0;
}

Workspace.prototype.selecttab = function(tab) {
    if (this.currenttab) {
        if (tab === this.currenttab) {
            return;
        }
        this.currenttab.hide();
    }
    tab.show();
    this.currenttab = tab;
}

Workspace.prototype.newtab = function(tabname) {
    var self = this;
    var tabmenu = document.getElementById("tabmenu");
    var li = document.createElement("li");
    tabmenu.appendChild(li);
    var a = document.createElement("a");
    li.appendChild(a);
    a.appendChild(document.createTextNode(tabname));
    a.href="#";
    a.addEventListener('click', function(event) {
        self.clicktab(event);
    });
    li.appendChild(document.createTextNode(" "));
    a2 = li.appendChild(document.createElement("a"));
    a2.href="#";
    a2.className = "close";
    a2.appendChild(document.createTextNode("×"));
    a2.addEventListener('click', function(event) {
        self.closetab(event);
    });
    this.tabcounter++;
    var contentid = "tab-" + this.tabcounter
    var div = document.getElementById("content")
        .appendChild(document.createElement("div"));
    div.id = contentid;
    div.style.display = "none";
    var tab = new Tab(this, li, contentid);
    this.tabs.push(tab);
    return tab;
}

Workspace.prototype.neweditortab = function(tabname) {
    var tab = this.newtab(tabname);
    if (this.editor) {
        // create a new session for an existing editor object
        tab.session = new EditSession('');
    } else {
        this.editor = ace.edit("editor");
        tab.session = this.editor.getSession();
    }
    var el = document.getElementById(tab.contentid);
    el.appendChild(document.createTextNode(tabname));
    return tab;
}

Workspace.prototype.loadfile = function(filename) {
    var tab = this.neweditortab(filename);
    var x = new XMLHttpRequest();
    var url = 'http://localhost:8080/git/' + filename;
    x.onreadystatechange = function() {
        if (x.readyState == 4) {
            tab.session.setValue(x.responseText);
        }
    };
    x.open('GET', url, true);
    x.send(null);
    return tab;
}

function foo() {
    var session = workspace.currenttab.session;
    document.getElementById("nav").className = "off";
    window.setTimeout(function () {document.getElementById("nav").className = "";}, 50);
    range = new Range(1, 4, 1, 7);
    session.addMarker(range, "gh_error", "text", false);
    session.setAnnotations([{row:0, column:10, text:"annotation text", type:"warning"}]);
    return false;
}

Workspace.prototype.clicktab = function(event) {
    var el = event.target.parentNode;
    for (var i = 0; i < this.tabs.length; i++) {
        var tab = this.tabs[i];
        if (el === tab.tabmenuelement) {
            this.selecttab(tab);
        }
    }
    event.preventDefault();
}

Workspace.prototype.closetab = function(event) {
    var el = event.target.parentNode;
    document.getElementById("tabmenu").removeChild(el);
    event.preventDefault();
}
