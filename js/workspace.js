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
var UndoManager = ace.require('ace/undomanager').UndoManager;

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
    // The filemap maps a file to either a string or a tab object (if there's
    // an open tab for the file).
    this.filemap = {};
    this.currenttab = null;
    this.tabcounter = 0;
    this.initmenus();
}

Workspace.prototype.initmenus = function() {
    var self = this;
    document.getElementById("menu-newtab").addEventListener('click',
        function (event) {
            self.selecttab(self.newtab('new tab'));
            self.finishmenuselect(event);
        });
    document.getElementById("menu-dirtab").addEventListener('click',
        function (event) {
            self.selecttab(self.newdirtab());
            self.finishmenuselect(event);
        });
    document.getElementById("menu-revert").addEventListener('click',
        function (event) {
            self.revert();
            self.finishmenuselect(event);
        });
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
        tab.session.setUndoManager(new UndoManager());
    } else {
        this.editor = ace.edit("editor");
        tab.session = this.editor.getSession();
    }
    var el = document.getElementById(tab.contentid);
    el.appendChild(document.createTextNode(tabname));
    return tab;
}

Workspace.prototype.loadfile = function(filename) {
    if (filename in this.filemap) {
        return this.filemap[filename];
    }
    var tab = this.neweditortab(filename);
    this.filemap[filename] = tab;
    var x = new XMLHttpRequest();
    var url = '/git/' + filename;
    x.onreadystatechange = function() {
        if (x.readyState == 4) {
            var contents = x.responseText;
            tab.original = contents;
            tab.session.setValue(contents);
        }
    };
    x.open('GET', url, true);
    x.send(null);
    return tab;
}

Workspace.prototype.deletetab = function(tab) {
    var ix = this.tabs.indexOf(tab);
    if (ix >= 0) {
        if (tab === this.currenttab) {
            if (ix > 0) {
                this.selecttab(this.tabs[ix - 1]);
            } else if (ix + 1 < this.tabs.length) {
                this.selecttab(this.tabs[ix + 1]);
            } else {
                tab.hide();
                this.currenttab = null;
            }
        }
        this.tabs.splice(ix, 1);
    }
    document.getElementById("tabmenu").removeChild(tab.tabmenuelement);
    document.getElementById("content").removeChild(
        document.getElementById(tab.contentid));
}

Workspace.prototype.revert = function() {
    var tab = this.currenttab;
    if (tab.session && tab.original !== undefined) {
        tab.session.setValue(tab.original);
    }
}

Workspace.prototype.newdirtab = function() {
    var self = this;
    var tab = this.newtab('dir');
    var x = new XMLHttpRequest();
    var url = '/workspace/_dir';
    x.onreadystatechange = function() {
        if (x.readyState == 4) {
            self.populatedir(tab.contentid, JSON.parse(x.responseText));
        }
    }
    x.open('GET', url, true);
    x.send(null);
    return tab;
}

Workspace.prototype.populatedir = function(id, dir) {
    var self = this;
    var container = document.getElementById(id);
    // container.style.overflow = 'scroll';
    function rec(dir, prefix) {
        for (var i = 0; i < dir.length; i++) {
            if (typeof dir[i] == 'string') {
                var div = container.appendChild(document.createElement('div'));
                var a = div.appendChild(document.createElement('a'));
                a.href = '#';
                var fn = prefix + dir[i];
                a.appendChild(document.createTextNode(fn));
                (function (fn) {
                    a.addEventListener('click', function(event) {
                        self.selecttab(self.loadfile(fn));
                        event.preventDefault();
                    })
                })(fn);
            } else {
                rec(dir[i][1], prefix + dir[i][0] + '/');
            }
        }
    }
    rec(dir, '');
}

Workspace.prototype.finishmenuselect = function(event) {
    document.getElementById("nav").className = "off";
    window.setTimeout(function () {document.getElementById("nav").className = "";}, 50);
    event.preventDefault();
}

function foo() {
    var session = workspace.currenttab.session;
    range = new Range(1, 4, 1, 7);
    session.addMarker(range, "gh_error", "text", false);
    session.setAnnotations([{row:0, column:10, text:"annotation text", type:"warning"}]);
    return false;
}

// Finds a tab object from the li element of the tab
Workspace.prototype.findtab = function(element) {
    for (var i = 0; i < this.tabs.length; i++) {
        var tab = this.tabs[i];
        if (element === tab.tabmenuelement) {
            return tab;
        }
    }
    return null;
}

Workspace.prototype.clicktab = function(event) {
    var tab = this.findtab(event.target.parentNode);
    if (tab) {
        this.selecttab(tab);
    }
    event.preventDefault();
}

Workspace.prototype.closetab = function(event) {
    var tab = this.findtab(event.target.parentNode);
    if (tab) {
        this.deletetab(tab);
    }
    event.preventDefault();
}
