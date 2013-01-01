# Copyright 2012 Google Inc.
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

# The workspace and generic edit area

import users
import gitcontent

import babygit.babygit

from webapp2_extras import json

class Handler(users.AuthenticatedHandler):
    def __init__(self, request, response):
        self.initialize(request, response)
        self.repo = gitcontent.get_repo()

    def get_workspace(self, arg):
        o = self.response.out
        o.write('''<!DOCTYPE html>
<html><head><title>Ghilbert workspace</title>
<link rel=stylesheet href="/static/editor.css" type="text/css">
</head>
<body class="fullscreen">
<ul id="nav">
    <li><a href="#">File</a>
        <ul>
            <li><a id="menu-newtab" href="#">New Tab</a></li>
            <li><a id="menu-dirtab" href="#">Directory</a></li>
            <li><a id="menu-revert" href="#">Revert</a></li>
            <li><a href="#">Save</a></li>
        </ul>
    </li>
    <li><a href="#">Edit</a>
        <ul>
            <li><a href="#" onclick="return foo();">Autoindent</a></li>
            <li><a href="#">Inline</a></li>
        </ul>
    </li>
</ul>

<!--<div style="height:1px; background: #000; clear:both"></div>-->

<ul id="tabmenu">
</ul>

<div id="editor" style="display: none"></div>

<div id="content"></div>

<script src="http://d1n0x3qji82z53.cloudfront.net/src-min-noconflict/ace.js" type="text/javascript" charset="utf-8"></script>
<script src="/js/workspace.js" type="text/javascript"></script>
<script type="text/javascript">
    var workspace = new Workspace();
''')
        if arg:
            o.write('    workspace.loadfile(' + json.encode(arg[1:]) + ');\n')
        o.write('    workspace.selecttab(workspace.newdirtab());\n')
        o.write('</script>\n')

    def ls(self, sha):
        result = []
        blob = self.repo.getobj(sha)
        if babygit.babygit.obj_type(blob) == 'tree':
            for mode, name, child_sha in self.repo.parse_tree(blob):
                if mode == '40000':
                    result.append([name, self.ls(child_sha)])
                else:
                    result.append(name)
        return result

    def get_dir(self):
        root = self.repo.getroot()
        self.response.headers['Content-Type'] = 'text/plain; charset = UTF-8'
        o = self.response.out
        o.write(json.encode(self.ls(root)))

    def get(self, arg):
        if arg == '/_dir':
            return self.get_dir()
        return self.get_workspace(arg)

