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

// A "tab" represents both an open tab (which may be associated with a
// file), or a "shelved" file, with contents but not an active editor.
function Tab(workspace) {
    this.workspace = workspace;
}

Tab.prototype.attachui = function(tabmenuelement, contentid) {
    this.tabmenuelement = tabmenuelement;
    this.contentid = contentid;
}

Tab.prototype.show = function() {
    document.getElementById(this.contentid).style.display = "block";
    if (this.session) {
        document.getElementById("editor").style.display = "block";
        this.workspace.editor.setSession(this.session);
        // Note: editor requires resize, but this is done in Workspace.resize()
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

Tab.prototype.shelve = function() {
    if (this.session) {
        this.contents = this.session.getValue();
    }
    this.session = undefined;
    this.tabmenuelement = undefined;
    this.contentid = undefined;
}

Tab.prototype.unshelve = function() {
    this.session.setValue(this.contents);
    this.contents = undefined;
}

// Get file contents of the tab (assuming it exists)
Tab.prototype.getcontents = function() {
    if (this.session) {
        return this.session.getValue();
    } else {
        return this.contents;
    }
}

Tab.prototype.setcontents = function(contents) {
    if (this.original === undefined) {
        this.original = contents;
    }
    if (this.session) {
        this.session.setValue(contents);
    } else {
        this.contents = contents;
    }
}

function Workspace() {
    // The tabs array only contains ui-attached tabs (not shelved files)
    this.tabs = [];
    // All files (whether mapped to ui or shelved)
    this.filemap = {};
    this.currenttab = null;
    this.tabcounter = 0;
    this.initmenus();
    var self = this;
    window.addEventListener('resize', function() {
        self.resize();
    });
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
    document.getElementById("menu-creatediff").addEventListener('click',
        function (event) {
            self.creatediff();
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
    this.resize();
}

Workspace.prototype.newtab = function(tabname, tab) {
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
    if (tab === undefined) {
        tab = new Tab(this);
    }
    tab.attachui(li, contentid);
    this.tabs.push(tab);
    return tab;
}

Workspace.prototype.neweditortab = function(tabname, tab) {
    var self = this;
    var tab = this.newtab(tabname, tab);
    if (!tab.session) {
        if (this.editor) {
            // create a new session for an existing editor object
            tab.session = new EditSession('');
            tab.session.setUndoManager(new UndoManager());
        } else {
            this.editor = ace.edit("editor");
            tab.session = this.editor.getSession();
        }
        tab.session.on('change', function(delta) {
            self.dirty();
        });
    }
    return tab;
}

Workspace.prototype.loadfile = function(filename) {
    if (filename in this.filemap) {
        var tab = this.filemap[filename];
        console.log(tab);
        if (tab.session) {
            return tab;
        }
    }
    var tabname = filename
    var slashix = tabname.lastIndexOf('/');
    if (slashix >= 0) {
        tabname = tabname.substring(slashix + 1);
    }
    tab = this.neweditortab(tabname, tab);
    if (tab.contents !== undefined) {
        tab.unshelve();
        return tab;
    }
    this.filemap[filename] = tab;
    var x = new XMLHttpRequest();
    var url = '/git/' + filename;
    x.onreadystatechange = function() {
        if (x.readyState == 4) {
            var contents = x.responseText;
            tab.setcontents(contents);
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
    tab.shelve();
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
    container.style.overflow = 'auto';
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

// Ideally, this should be done with flexboxes, but I can't figure it out.
Workspace.prototype.resize = function() {
    var height = window.innerHeight;
    height -= document.getElementById("nav").offsetHeight;
    height -= document.getElementById("tabmenu").offsetHeight;
    var tab = this.currenttab;
    if (tab.session) {
        document.getElementById("editor").style.height = height + "px";
        this.editor.resize();
    } else {
        document.getElementById(tab.contentid).style.height = height + "px";
    }
}

Workspace.prototype.getdiff = function() {
    var diffs = [];
    var d = new diff_match_patch();
    for (var fn in this.filemap) {
        var tab = this.filemap[fn];
        if (tab.original !== undefined) {
            var diff = d.patch_make(tab.original, tab.getcontents());
            diffs.push([fn, diff]);
        }
    }
    // TODO: keep track of base sha and maybe timestamp
    return {"diffs": diffs};    
}

Workspace.prototype.creatediff = function() {
    var diffs = this.getdiff();
    var tab = this.newtab("diff");
    var div = document.getElementById(tab.contentid)
        .appendChild(document.createElement('div'));
    div.appendChild(document.createTextNode(JSON.stringify(diffs)));
    this.selecttab(tab);
}

// Call this method every time there's a mutation to the workspace (which
// would trigger a save.
Workspace.prototype.dirty = function() {
    // TODO: more logic to defer dirty if XHR is in flight
    var self = this;
    if (this.dirtytimeoutid !== undefined) {
        window.clearTimeout(this.dirtytimeoutid);
    }
    this.dirtytimeoutid = window.setTimeout(function() {
        var diffs = self.getdiff();
        var x = new XMLHttpRequest();
        x.open('POST', '/workspace', true);
        x.setRequestHeader('Content-Type', 'application/json; charset=UTF-8');
        x.onreadystatechange = function() {
            // TODO; track in-flight status
        };
        x.send(JSON.stringify(diffs));
        self.dirtytimeoutid = undefined;
    }, 2000);
}