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
import binascii
import logging
import urllib
import webapp2

from google.appengine.ext import db
from webapp2_extras import sessions

import common
import gitcontent

class User(db.Model):
    # key_name is userid
    identity = db.StringProperty()
    ctime = db.DateTimeProperty(auto_now=True)
    pwsalt = db.StringProperty()
    pwhash = db.StringProperty()

    # None/empty for new users, "write", or "super"
    perms = db.StringProperty()

class AuthenticatedHandler(webapp2.RequestHandler):
    def dispatch(self):
        self.session_store = sessions.get_store(request=self.request)
        try:
            webapp2.RequestHandler.dispatch(self)
        finally:
            self.session_store.save_sessions(self.response)

    @webapp2.cached_property
    def session(self):
        return self.session_store.get_session(backend='datastore')

    @webapp2.cached_property
    def username(self):
        session = self.session
        if not session:
            return None
        return session.get('uid')

    @webapp2.cached_property
    def userobj(self):
        username = self.username
        if not username:
            return None
        return User.get_by_key_name(username)

    @webapp2.cached_property
    def perms(self):
        user = self.userobj
        if not user:
            return None
        return user.perms

    @webapp2.cached_property
    def has_write_perm(self):
        perms = self.perms
        return perms and perms == 'super' or perms == 'write'

class AccountHandler(AuthenticatedHandler):
    def serve_createaccount(self):
        o = self.response.out
        common.header(o, 'Create account')
        invitecode = self.request.get('invite')
        entropy = binascii.b2a_base64(os.urandom(18))
        o.write('''<form method="post" action="/account/create">\n
<div>Username: <input type="text" name="username"></div>
<div>Password: <input type="password" name="password"></div>
<div>Password again: <input type="password" name="password2"></div>
<div>Git identity: <input type="text" name="identity"></div>
<input type="hidden" name="invite" value="%s">
<input type="submit" value="Create">
''' % urllib.quote(invitecode))
        templ = gitcontent.get_wiki_html('CreateAccountTempl')
        if templ is None:
            templ = "[Warning: CreateAccountTempl is missing]"
        o.write(templ.replace('$entropy', entropy))

    def serve_login(self):
        o = self.response.out
        common.header(o, 'Login')
        o.write('''<form method="post" action="/account/login">\n
<div>Username: <input type="text" name="username"></div>
<div>Password: <input type="password" name="password"></div>
<input type="submit" value="Login">
<div>Or <a href="/account/CreateAccount">create an account</a> if you don't have one.</div>
''')

    def serve_logout(self):
        o = self.response.out
        common.header(o, 'Logged out')
        o.write('successfully logged out')
        if 'uid' in self.session:
            del self.session['uid']

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
        salt = binascii.hexlify(os.urandom(16))
        user.pwsalt = salt
        user.pwhash = hashlib.sha1(salt + passwd).hexdigest()
        invite_salt = 'c1e3d755b19119fb'
        invitecode = self.request.get('invite')
        invite_hash = 'fd88b74e489c03fcfbf799a1b6d1b00169f6f24b'
        if hashlib.sha1(invite_salt + invitecode).hexdigest() == invite_hash:
            user.perms = 'write'
            o.write('<p>Invite code is valid, congratulations!</p>\n')
        user.put()
        o.write('Account ' + username + ' created.\n')
        self.session['uid'] = username

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
        if not check_user_pass(user, passwd):
            return self.errmsg('password doesn\'t match')
        self.session['uid'] = username
        o.write('Login ok!')

    def get(self, arg):
        if not request_secure_enough(self.request):
            url = self.request.url
            if url.startswith('http:'):
                return self.redirect('https:' + url[5:])
            else:
                return None
        if arg == 'CreateAccount':
            self.serve_createaccount()
        elif arg == 'Login':
            self.serve_login()
        elif arg == 'Logout':
            self.serve_logout()
    def post(self, arg):
        if arg == 'create':
            self.serve_createaction()
        elif arg == 'login':
            self.serve_loginaction()

def check_pass(username, passwd):
    user = User.get_by_key_name(username)
    if not user:
        return False
    return check_user_pass(user, passwd)

def check_perms(username, desired_perms):
    user = User.get_by_key_name(username)
    if not user or not user.perms:
        return False
    if user.perms == 'super':
        return True
    return user.perms == desired_perms

def check_user_pass(user, passwd):
    return user.pwhash == hashlib.sha1(user.pwsalt + passwd).hexdigest()

# Allow http requests from the dev server, require https otherwise
def request_secure_enough(request):
    return request.environ['SERVER_SOFTWARE'].startswith('Development') or \
        request.environ.get('HTTPS') == 'on'

# The front page (/) is in this module because it's sensitive to login state
class FrontPageHandler(AuthenticatedHandler):
    def get(self):
        o = self.response.out
        common.header(o, 'Ghilbert home')
        userobj = self.userobj
        if userobj is not None:
            template = 'FrontPageLogged'
        else:
            template = 'FrontPage'
        content = gitcontent.get_wiki_html(template)
        if content is None: content = '[wiki template for ' + template + ' is missing]'
        o.write(content)

