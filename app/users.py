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

# Management of user accounts and profiles

import re
import os
import hashlib
import logging

import babygit.babygit  # for to_hex

from google.appengine.ext import db
from google.appengine.ext import webapp

import common

class User(db.Model):
    # key_name is userid
    identity = db.StringProperty()
    ctime = db.DateTimeProperty(auto_now=True)
    pwsalt = db.StringProperty()
    pwhash = db.StringProperty()

class AccountHandler(webapp.RequestHandler):
    def serve_createaccount(self):
        o = self.response.out
        common.header(o, 'Create account')
        o.write('''<form method="post" action="/account/create">\n
<div>Username: <input type="text" name="username"></div>
<div>Password: <input type="password" name="password"></div>
<div>Password again: <input type="password" name="password2"></div>
<div>Git identity: <input type="text" name="identity"></div>
<input type="submit" value="Create">
<p>Some notes:</p>
<p>Username must be alphanumeric, with _ also allowed.</p>

<p>Ideally use a random generator for your password. You will likely be
storing it in your .netrc anyway. Please don't use one that is easily
guessable, or shared with other accounts.</p>

<p>Your Git identity should be of the form "Name <email@addr>", and is
public. Choose an email address that's good at filtering spam (although
it doesn't strictly have to be a valid, deliverable address).</p>
''')

    def serve_login(self):
        o = self.response.out
        common.header(o, 'Login')
        o.write('''<form method="post" action="/account/login">\n
<div>Username: <input type="text" name="username"></div>
<div>Password: <input type="password" name="password"></div>
<input type="submit" value="Login">
''')

    def errmsg(self, msg):
        self.response.out.write('error: ' + msg)

    valid_username = re.compile('[a-zA-Z0-9_]+$')
    valid_identity = re.compile('[^<]+\s+<[^>]+>$')
    def serve_createaction(self):
        o = self.response.out
        common.header(o, 'Account creation results')
        username = self.request.get('username')
        passwd = self.request.get('password')
        identity = self.request.get('identity')
        if len(username) < 1: return self.errmsg('username must be nonempty')
        if not self.valid_username.match(username):
            return self.errmsg('username must be alphanumeric with _')
        if len(passwd) < 6: return self.errmsg('password must be at least 6 characters')
        if passwd != self.request.get('password2'):
            return self.errmsg('passwords don\'t match')
        if not self.valid_identity.match(identity):
            return self.errmsg('identity must be of the form Name &lt;email&gt;')
        if User.get_by_key_name(username):
            return self.errmsg('account ' + username + ' already exists')
        user = User(key_name = username)
        user.identity = identity
        salt = babygit.babygit.to_hex(os.urandom(16))
        user.pwsalt = salt
        user.pwhash = hashlib.sha1(salt + passwd).hexdigest()
        user.put()
        o.write('Account ' + username + ' created.')

    def serve_loginaction(self):
        o = self.response.out
        common.header(o, 'Login results')
        username = self.request.get('username')
        passwd = self.request.get('password')
        if not self.valid_username.match(username):
            return self.errmsg('username must be alphanumeric with _')
        user = User.get_by_key_name(username)
        if not user:
            return self.errmsg('no such user exists')
        logging.debug(`(user.pwhash, hashlib.sha1(user.pwsalt + passwd))`)
        if user.pwhash != hashlib.sha1(user.pwsalt + passwd).hexdigest():
            return self.errmsg('password doesn\'t match')
        o.write('Login ok!')

    def get(self, arg):
        if arg == 'CreateAccount':
            self.serve_createaccount()
        elif arg == 'Login':
            self.serve_login()
    def post(self, arg):
        if arg == 'create':
            self.serve_createaction()
        elif arg == 'login':
            self.serve_loginaction()

