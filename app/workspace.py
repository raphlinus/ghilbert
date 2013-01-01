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

from webapp2_extras import json

class Handler(users.AuthenticatedHandler):
    def __init__(self, request, response):
        self.initialize(request, response)
        self.repo = gitcontent.get_repo()

    def get(self, arg):
        o = self.response.out
        o.write('''<!DOCTYPE html>
<html><head><title>Ghilbert workspace</title>
<link rel=stylesheet href="/static/editor.css" type="text/css">
</head>
<body class="fullscreen">
<ul id="nav">
    <li><a href="#">File</a>
        <ul>
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

<div id="editor"></div>

<div id="content"></div>

<script src="http://d1n0x3qji82z53.cloudfront.net/src-min-noconflict/ace.js" type="text/javascript" charset="utf-8"></script>
<script src="/js/workspace.js" type="text/javascript"></script>
<script type="text/javascript">
    var workspace = new Workspace();
''')
        if len(arg):
            o.write('    workspace.loadfile(' + json.encode(arg[1:]) + ');\n')
        o.write('    workspace.selecttab(workspace.loadfile("bar"));\n')
        o.write('</script>\n')


