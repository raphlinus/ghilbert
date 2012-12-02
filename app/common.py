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

# Stuff common to most pages on the webapp (includes hardcoded templates)

import cgi

def header(o, name, stylesheet = None):
    o.write('<html><head><title>' + cgi.escape(name) + '</title>\n')
    if stylesheet:
    	o.write(stylesheet)
    o.write('<link rel=stylesheet href="/static/common.css" type="text/css">\n')
    o.write('<body>\n')
    o.write('<div class="header">')
    o.write('<a href="/"><img src="/static/favicon.ico"/></a> <a href="/">Ghilbert</a>')
    o.write('</div>')
    o.write('<h1>' + cgi.escape(name) + '</h1>\n')

def error_403(handler):
    handler.error(403)
    header(handler.response.out, 'Forbidden')
    handler.response.out.write('Sorry, you\'re not authorized. Maybe <a href="/account/Login">login</a>?')

