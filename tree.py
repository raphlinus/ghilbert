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

from google.appengine.api import users
from google.appengine.ext import webapp
from google.appengine.ext.webapp.util import run_wsgi_app
from google.appengine.ext import db

from django.utils import simplejson

class Player(db.Model):
    name = db.StringProperty()
    lastSeen = db.DateTimeProperty(auto_now=True)
    score = db.IntegerProperty()
    location = db.StringProperty()
    goal = db.StringProperty()

class StatusJs(webapp.RequestHandler):
    def get(self, name):
        player = Player.get_or_insert(name)
        if (player.location is None):
            player.score = 0
            player.location = "Propcal"
            player.goal="(&#x2192; A (&#x2192; B B))"
            player.name = name
        self.response.out.write("""
({
score: %s,
location: "%s",
goal: "%s",
name: "%s",
})
""" % (player.score, player.location, player.goal, player.name));


application = webapp.WSGIApplication(
                                     [('/tree/status/(.*)', StatusJs),
                                      ],
                                     debug=True)

def main():
    run_wsgi_app(application)

if __name__ == "__main__":
    main()
