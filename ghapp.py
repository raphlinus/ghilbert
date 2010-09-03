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
from google.appengine.ext.db import stats # DLK debug
from google.appengine.ext.webapp.util import run_wsgi_app
from google.appengine.ext import db

from django.utils import simplejson as json

# Only supports strings and lists now.
def json_dumps(obj):
    if type(obj) in (str, unicode):
        obj = obj.replace('\\', '\\\\')
        obj = obj.replace('"', '\\"')
        return '"' + obj + '"'
    elif type(obj) == list:
        return "[" + ", ".join(map(json_dumps, obj)) + "]"
    else:
        return 'null'

# DLK just thinking...
#
# How much does the database structure need to reflect the structure
# in the Ghilbert universe?
# I think we want the module to read the whole database and keep
# the results cached, pre-parsed, for subsequent requests.
# Need to worry about accesses to the database by multiple processes,
# however.

class StringScanner(object):

    def __init__(self, text, lineno=1):
        if isinstance(text, str):
            self.text = text
        else:
            self.text = text.encode('ascii')
        self.start_ix = 0
        self.ix = 0
        self.lineno = 1

    def get_tok(self):
        ix = self.ix
        text = self.text
        l = len(text)
        in_comment = False
        tok_start = None
        while ix < l:
            ch = text[ix]
            n = ord(ch)
            if n >= 127 or (n < 32 and ch not in '\n\r'):
                raise SyntaxError('Invalid character 0x%x in text' % n)
            if in_comment:
                if (ch == '\n' or
                    ch == '\r' and (ix + 1 == l or text[ix + 1] != '\n')):
                    in_comment = False
                    self.lineno += 1
                ix += 1
                continue
            if ch in ' ()#\r\n':
                if tok_start is not None:
                    self.ix = ix
                    return text[tok_start:ix]
                if ch in '()':
                    self.ix = ix + 1
                    return ch
                if ch == '#':
                    in_comment = True
                elif (ch == '\n' or
                      ch == '\r' and (ix + 1 == l or text[ix + 1] != '\n')):
                    self.lineno += 1
            elif tok_start is None:
                tok_start = ix
            ix += 1
            continue
        self.ix = ix
        if tok_start is None:
            return None
        return text[tok_start:ix]

    def end_record(self):
        start_ix = self.start_ix
        ix = self.ix
        self.start_ix = ix
        return self.text[start_ix:ix]

def number_to_key(n):
    """ n must be an integer (or long) greater than 0, of fewer than 100
        decimal digits. Return a string representation of n that preserves
        ordering, when using the usual lexicographical ordering on strings.
    """
    if n <= 0:
        raise ValueError('number_to_key() argument must be > 0')
    w = 1
    p = 10
    while n >= p:
        w += 1
        p *= 10
    if w >= 100:
        raise ValueError('number_to_key() argument must be have fewer than 100 digits when expressed as a decimal number.')
    return '%02d:%d' % (w, n)

def key_to_number(kstr):
    """ This function is a left-inverse to number_to_key().
        That is, key_to_number(number_to_key(n)) == n for non-negative
        intergers n in the domain of number_to_key().
    """
    return int(kstr[3:])

    
# Every Generation entity in the datastore is top-level; it has no
# ancestors.
#
#  - A given Generation entity corresponds to a sequence (i.e. a 'log') of
#    GHLogEntry entities, that all have the Generation entity as their
#    parent. If there is more than one Generation entity, they are
#    distinguished by their 'gen' value, which is non-negative. Generation
#    entities with higher 'gen' values are more _recent_ than Generation
#    entities with lower 'gen' values.
#  - If an app instance detects that its current Generation item no
#    longer exists in the datastore, or if the app instance does not yet
#    have a current Generation item, it should query for the most recent
#    Generation item in the datastore, and start using that.  In fact,
#    each time an app services a request, it should update to the latest
#    Generation.
#  - When extending a log, an app should do the following within a transaction:
#    - read the current edit generation by key from the datastore, to verify
#      that it still exists.
#    - query for GHLogEntry descendants of the current Generation
#      whose log entry numbers are greater than or equal to the next
#      expected log entry number (i.e., the last read log entry number plus
#      1).  The query should return no results. (Should we use a key name
#      instead? We can use a string key that corresponds with the 
#        0 :1 :2 :3 :4 :5 :6 :7 :8 :9 ::10 ::11 ... ::99 :::100 ... :::999
#        ::::1000 ... ::::9999 :::::10000
#       Ways of encoding non-negative integers as strings that preserve
#       ordering, using the lexicographical ordering on strings.
#       00: 01:1 ... 01:9 02:10 ... 02:99 03:100 ... 03:999
#       04:1000 ... 04:9999 05:10000 ... 05:99999 06:100000 ... 06:999999
#       all the way up to 99:99...9 (99 9's after the :). Given that integer
#       properties fit in 64 bits, that's more than enough range.
#
#  - If the Generation item has gen = 0, the datastore is in the
#    process of being administratively updated, and the datastore state
#    may be inconsistent.  Client requests should wait until the gen value
#    of the Generation becomes non-zero.
#  - All valid GHLogEntries have the current EditGenertation item as
#    their parent.
class Generation(db.Model):
    """ The key name for a Generation entity is the generation number, encoded
        with number_to_key().
    """
    # to_do is greater than zero while the Generation is being initialized.
    # basis is a json list the default files used to initialize the Generation
    # and context names (null except for verify context files).
    # to_do starts at the length of the list represented by base, and
    # decreases down to zero as the initialization procedes.
    to_do = db.IntegerProperty(required=True)
    basis = db.TextProperty()

def latest_generation():
    """ Returns the latest initialized Generation entity object in the
        datastore.
    """
    q = Generation.all()
    latest = None
    # Ordered by key...
    for gen in q:
        if gen.to_do == 0:
            latest = gen
    return latest

def all_generations():
    q = db.Query(Generation, keys_only=True)
    gen_nums = []
    for key in q:
        name = key.name()
        gen = key_to_number(name)
        gen_nums.append(gen)
    return gen_nums

def get_generation(num):
    gen_name = number_to_key(num)
    key = db.Key.from_path('Generation', gen_name)
    return db.get(key)

def next_generation(gen_list):
    gen = 1
    for g in gen_list:
        if g >= gen:
            gen = g + 1
    return gen

class EditGeneration(db.Model):
    gen = db.IntegerProperty(required=True)

# Can the Generation idea be race-free?

class GHLogEntry(db.Model):
    """ The key name for a GHLogEntry entity is its 1-based index in
        the log, encoded with number_to_key().
    """
    context_index = db.IntegerProperty(required=True)
    command = db.StringProperty(required=True)
    data = db.TextProperty() # Maybe use BlobProperty instead?
    author = db.UserProperty(auto_current_user_add=True)
    date = db.DateTimeProperty(auto_now_add=True)

# GHLogEntry commands
# 'new_interface_context'
#   - context_index is the number of new contexts introduced earlier in the
#     log. Equivalently, it is the index of the context being introduced.
#   - data contains the interface context path (e.g. '/peano/pred_ax.ghi')
# 'new_proof_context_named: <VerifyContextName>'
#   - context_index is the number of new contexts introduced earlier in the
#     log. Equivalently, it is the index of the context being introduced.
#   - data contains the proof context path (e.g. '/peano/peano_thms.gh')
# 'extend'
#   - context_index identifies the earlier-introduced context to be extended.
#   - data contains a number of ghilbert commands (comments allowed) to
#     append to the specified context. Individual ghilbert commands should
#     not be split between extend entries.
# 'replace: <starting_command_num> until: <stopping_command_num>'
#   - context_index identifies the earlier-introduced context to be modified
#   - data contains a number of ghilbert commands.  These replace the ghilbert
#     commands of the affected context, starting with <starting_command_num>
#     up to but not including <stopping_command_num>. Any comments (and non-
#     initial whitespace) preceding a command are considered part of the
#     command.
#     The first ghilbert command in a context has number zero.
#     <starting_command_num> and <stopping_command_num> are non-negative
#     decimal numbers, consisting of the characters [0-9]. They must be
#     in the range from 0 to the current number of commands in the affected
#     context, and <starting_command_num> must not be greater than
#     <stopping_command_num>.
#     Note that an 'extend' log entry is equivalent to a 'replace' log
#     entry specifying a <starting_command_num> and a <stopping_command_num>
#     equal to the current number of commands in the context. Insertion before
#     command number <N> in the context is done as 'replace: <N> until: <N>'.

# Some use cases:
# - Add a variable to a context.
# - Prove a theorem in a context.
# - Prove a defthm in a context, adding the defined term and statement.
# - Edit an existing theorem or defthm, preserving its interface.
#   (Need to ensure that the new proof doesn't depend upon results proven
#   later that depend on it.  If the theorem is relocated in the context
#   sequence, need to make sure it is not moved after any other results that
#   depend on it. But the linear sequence is a bit artificial.)
# - Add a new proof of a statement within a different context.
# - Add an unproven statement as an axiom, creating a larger context.
#   (Probably want to be able to add several at once, so as not need to name
#    all the intermediate ones...)
# - If a context has axioms that turn out to be provable based upon
#   the parent context (or other axioms of the same context), such axioms
#   may be removed as explicit dependencies of the context.
# - Dump the full database to a client. Probably need to break in pieces
#   to avoid quota limits.
# - Recreate the database based upon input files, or extend the database
#   using bulk updates based upon input files.

# (Current generation number, Generation object)
gh_gen = None

def clear_datastore(maxitems=0):
    logging.warning('***** Clearing Datastore! *****')
    items = 0
    classes = (EditGeneration, Generation, GHLogEntry)
    for cl in classes:
        q = cl.all()
        for item in q:
            item.delete()
            items += 1
            if maxitems != 0 and items >= maxitems:
                return False
    return True

def clear_generation(gen_num, maxitems=0):
    logging.warning('***** Clearing Generation %d *****' % gen_num)
    gen_name = number_to_key(gen_num)
    k = db.Key.from_path('Generation', gen_name)
    q = GHLogEntry.all()
    q.ancestor(k)
    items = 0
    for item in q:
        item.delete()
        items += 1
        if maxitems != 0 and items >= maxitems:
            logging.warning('... cleared %d items' % items)
            return False
    logging.warning('... cleared %d items' % items)
    gen = db.get(k)
    if gen is not None:
        gen.delete()
    return True

def GHAddFile(name, path, parent, index):
    global gh_base_dir
    # TODO: check that path starts with '/'.
    # TODO: check that name is a valid atom (interface name) & unique!
    logging.info('GHAddFile %s, %s' % (name, path))
    full_pname = os.path.join(gh_base_dir, path[1:])
    fd = None
    try:
        try:
            fd = open(full_pname, mode='r')
        except IoError, e:
            raise
        content = fd.read() # returns string, not Unicode string
        if len(content) > 500000: # actual limit is currently 1MB.
            raise ValueError('File %s too big for datastore' % full_pname)
        command = ('new_interface_context' if name is None
                   else 'new_proof_context_named: %s' % name)
        ctx_no = index
        num = index * 2 + 1  # use 1-based index for key_name
        entry_name = number_to_key(num)
        entry = GHLogEntry(context_index=ctx_no,
                           command=command,
                           data=path,
                           parent=parent,
                           key_name=entry_name)
        entry.put()
        num = index * 2 + 2
        entry_name = number_to_key(num)
        entry = GHLogEntry(context_index=ctx_no,
                           command='extend',
                           data=content,
                           parent=parent,
                           key_name=entry_name)
        entry.put()
    finally:
        if fd is not None:
            fd.close()

def gh_generation_create_cb(gen_num, defaults):
    gen = get_generation(gen_num)
    if gen is None:
        gen_name = number_to_key(gen_num)
        gen = Generation(to_do=len(defaults),
                         basis=json.dumps(defaults),
                         key_name=gen_name)
        gen.put()
    else:
        basis = json.loads(gen.basis)
        if basis != defaults:
            logging.info('Conflicting bases for generation creation')
            raise Rollback('Conflicting bases for generation creation')

    n = gen.to_do
    if n == 0:
        return 'done'
    if n < 0 or n > len(defaults):
        raise Rollback('Invalid to_do count.')
    name, path = defaults[-n]
    GHAddFile(name, path, gen, len(defaults) - n)
    n -= 1
    gen.to_do = n
    gen.put()
    return path
    
        
def GHGenerationCreate(gen_num, defaults):
    res = db.run_in_transaction(gh_generation_create_cb, gen_num, defaults)
    return res

class DummyWriter(object):
    def __init__(self):
        pass
    def write(self, data):
        logging.info('%s' % data)
        return

dummy_writer = DummyWriter()

class GHDatastoreError(Exception):
    def __init__(self, why):
        Exception.__init__(self, why)
        self.why = why

def gh_gen_refresh():
    global gh_gen
    gen = latest_generation()
    gh_gen = gen
    return gen
    
gh_updater = None

def GHDatastoreUpdate(maxitems, out=None):
    """ Attempt to (partially) update the verifier datastructures based
        upon the current datastore contents.
        - Returns 'done' if the verifier datastructures were brought up to
          the current state (however briefly)
        - Returns 'again' if the verifier datastructures are not yet up to
          current. Client should call again.
        - Returns 'wait' if the datastore is currently empty or being
          reinitialized
    """
    global gh_updater

    gen = latest_generation()
    if gen == None:
        logging.info ("No Generation!")
        gh_updater = None
        return 'wait'

    logging.info ("latest gen: %s" % gen.key().name())
    if gh_updater is not None:
        if gh_updater.current_gen.key() != gen.key():
            logging.info ("update key mismatch, restarting")
            gh_updater = None

    if gh_updater is None:
        logging.info ("Creating new GHUpdater")
        gh_updater = GHUpdater(maxitems, gen)

    if out is None:
        out = DummyWriter()

    if gh_updater.read_datastore(out):
        return 'done'
    
    # TODO: catch other exceptions?
    return 'again'

class GHUpdater(object):
    def __init__(self, maxitems, gen):
        self.maxitems = maxitems
        self.next_entry_number = 1
        self.context_list = []
        self.context_dict = {}
        self.ctx_in_progress = {}
        self.current_gen = gen

    def read_datastore(self, out):
        global gh_base_dir

        logging.info('Reading log from #%d' % self.next_entry_number)
        self.out = out

        count = 0
        while True:
            entry_name = number_to_key(self.next_entry_number)
            ekey = db.Key.from_path('GHLogEntry', entry_name,
                                 parent=self.current_gen.key())
            entry = db.get(ekey)
            if entry is None:
                break
            self.read_entry(entry)
            self.next_entry_number += 1
            count += 1
            if count >= self.maxitems:
                return False
        #logging.info('read_datastore done, count=%d' % count)
        return True

    def lookup_context(self, norm_path):
        """ Given a normalized path, look up the corresponding ghilbert
            context.
              Returns (None, False) if there is no such context.
              Returns (ctx, False) if the context was found directly.
              Returns (ctx, True) if the context was found as the automatically
                generated export from a proof file context.
        """
        pif = self.context_dict.get(norm_path)
        if pif is not None:
            return pif, False
        if norm_path.endswith('.ghi'):
            pif = self.context_dict.get(norm_path[:-1])
            if pif is None or pif.name is None:
                return None, False
            return pif, True
        return None, False

    def normalize(self, url, caller_fname):
        global gh_base_dir
        if url[0] == '/':
            fn = os.path.join(gh_base_dir, url[1:])
        else:
            # caller_fname is already normalized.
            caller_dir = os.path.split(caller_fname)[0]
            caller_dir = os.path.join(gh_base_dir, caller_dir[1:])
            fn = os.path.join(caller_dir, url)
        fn = os.path.realpath(fn)
        if not fn.startswith(gh_base_dir + '/'):
            raise verify.VerifyError('Bad interface url: %s' % url)
        return fn[len(gh_base_dir):]

    def fetch_interface(self, url, caller_ctx):
        fn = self.normalize(url, caller_ctx.fname)
        # TODO: These recursion guards are not foolproof. Could have mutually
        # recursive imports by verify contexts...
        if fn in self.ctx_in_progress:
            raise VerifyError('Interface %s recursively fetched')
        pif = self.context_dict.get(fn)
        if pif is None:
            if fn.endswith('.ghi'):
                fnp = fn[:-1]
                if fnp in self.ctx_in_progress:
                    raise verify.VerifyError('Interface %s recursively fetched')
                pif = self.context_dict.get(fnp)
                if pif.name is None:
                    pif = None
            if pif is None:
                raise verify.VerifyError('Interface %s (%s) not found' %
                                         (url, fn))
            pif.importers[caller_ctx.fname] = caller_ctx
        else:
            if pif.name is not None:
                raise verify.VerifyError('Attempt to use proof file context as interface file: %s' % url)
        # Note, we rely on having contexts defined before they are used,
        # so we don't need to 'build' an interace context here.
        if pif.level >= caller_ctx.level:
            caller_ctx.level = pif.level + 1

        return pif

    def start_context(self, ctx):
        self.ctx_in_progress[ctx.fname] = ctx

    def read_entry(self, entry):
        global gh_base_dir

        """ Evaluate the command in the GHLogEntry entity entry"""
        entry_num = self.next_entry_number
        command = entry.command
        ctx_ix = entry.context_index
        if (command == 'new_interface_context' or
            command.startswith('new_proof_context_named: ')):
            if ctx_ix != len(self.context_list):
                raise GHDatastoreError(
                    "In log entry #%d, expected new context %d but found %d" %
                    (entry_num, self.new_context_index, ctx_ix))
            path = entry.data.encode('ascii')
            if len(path) < 1 or path[0] != '/':
                raise GHDatastoreError(
                    'Invalid context path in log entry #%d: %s' %
                    (entry_num, path))
            norm_path = self.normalize(path, '/')
            if norm_path in self.context_dict or path in self.ctx_in_progress:
                raise GHDatastoreError(
                    "Duplicate context '%s' created in log entry #%d" %
                    (norm_path, entry_num))

            if command == 'new_interface_context':
                gh_ctx = verify.InterfaceCtx(self, norm_path)
            else: # proof file context
                gh_ctx = verify.VerifyCtx(self, norm_path, False)
                cname = command[len('new_proof_context_named: '):]
                # TODO: check that cname is a valid context name...
                gh_ctx.name = cname.encode('ascii')
                gh_ctx.importers = {}
            gh_ctx.verbosity = 0
            gh_ctx.out = DummyWriter()
            gh_ctx.cmd_hist = []
            gh_ctx.context_index = ctx_ix
            self.context_list.append(gh_ctx)
            return
        elif command == 'extend':
            try:
                gh_ctx = self.context_list[ctx_ix]
            except IndexError:
                raise GHDatastoreError(
                    'Invalid context index %d in extend at log entry #%d' %
                    (ctx_ix, entry_num))
            norm_path = gh_ctx.fname
            self.ctx_in_progress[norm_path] = gh_ctx
            scanner = StringScanner(entry.data)
            self.run(scanner, norm_path, gh_ctx)
            del self.ctx_in_progress[norm_path]
            self.context_dict[norm_path] = gh_ctx
            # For now we assume extension only occurs by single thm/defthm,
            # with the label checked for no possibility of conflict with
            # symbols in dependent contexts.  So we skip the dependent
            # context reprocessing.
            return
        elif command[:8] == 'replace:':
            l = command.split()
            try:
                start = long(l[1])
                stop = long(l[3])
            except:
                raise GHDatastoreError("Invalid command '%s'" % command)
            try:
                gh_ctx = self.context_list[ctx_ix]
            except IndexError:
                raise GHDatastoreError(
                    'Invalid context index %d in extend at log entry #%d' %
                    (ctx_ix, entry_num))
            maxcmd = len(gh_ctx.cmd_hist) / 4
            if (start < 0 or start > stop or stop > maxcmd):
                raise GHDatastoreError(
                    'Bad command indices (max %d) in %s' % (maxcmd, command))
            tail = gh_ctx.cmd_hist[(stop*4):(maxcmd*4)]
            norm_path = gh_ctx.fname
            self.ctx_in_progress[norm_path] = gh_ctx
            gh_ctx.undo_to(start)
            scanner = StringScanner(entry.data)
            self.run(scanner, norm_path, gh_ctx)
            gh_ctx.apply_hist(tail)
            del self.ctx_in_progress[norm_path]
            self.context_dict[norm_path] = gh_ctx
        else:
            raise GHDatastoreError("Unhandled log entry #%d, command: %s" %
                                   (entry_num, command))
        
        if gh_ctx.name is None:
            return

        # Reverify any dependent contexts
        # Note, we need to do dependent interface contexts also!
        # TODO: report errors...
        for ctx in self.context_list:
            if ctx.fname not in gh_ctx.importers:
                continue
            logging.info('Reprocessing %s\n' % ctx.fname)
            hist = ctx.cmd_hist[:]
            ctx.undo_to(0)
            self.ctx_in_progress[ctx.fname] = ctx
            ctx.apply_hist(hist)
            del self.ctx_in_progress[ctx.fname]
        
    def run(self, scanner, url, ctx):
        read_sexp = verify.read_sexp
        while 1:
            cmd = verify.read_sexp(scanner)
            if cmd is None:
                return True
            if not isinstance(cmd, str):
                logging.error('Command word is not string: %s' %
                              verify.sexp_to_string(cmd))
                continue
            arg = read_sexp(scanner)
            if not isinstance(arg, list):
                logging.error('Command argument is not list: %s' % cmd)
                continue
            try:
                ctx.do_cmd(cmd, arg, scanner.end_record())
            except verify.VerifyError, x:
                ctx.record_error('Verify error: %s' % x.why)
            except SyntaxError, x:
                ctx.record_error('Syntax error: %s' % str(x))
        return True

    def datastore_logentry_cb(self, ctx_ix, command, content):
        gen = self.current_gen
        gkey = gen.key()
        gen = db.get(gkey)
        if gen is None:
            raise db.Rollback('Generation %s no longer exists.' % gkey.name())
        num = self.next_entry_number
        entry_name = number_to_key(num)
        ekey = db.Key.from_path('GHLogEntry', entry_name, parent=gkey)
        entry = db.get(ekey)
        if entry is not None:
            # should we try to read to the end of the log here?
            raise db.Rollback('Not at current end of log!')
        
        entry = GHLogEntry(context_index=ctx_ix,
                           command=command,
                           data=content,
                           parent=gen,
                           key_name=entry_name)
        entry.put()
        # Note, do not increment self.next_entry_number here!
        return True

    def ctx_cmds_add(self, ctx_ix, content):
        res = db.run_in_transaction(self.datastore_logentry_cb,
                                    ctx_ix, 'extend', content)
        return res


    def ctx_cmds_replace(self, ctx_ix, start, stop, new_content):
        ctx = self.context_list[ctx_ix]
        maxcmd = len(ctx.cmd_hist) / 4
        assert (0 <= start <= stop <= maxcmd)
        command = 'replace: %d until: %d' % (start, stop)
        res = db.run_in_transaction(self.datastore_logentry_cb,
                                    ctx_ix, command, new_content)
        return res
        
def theorem_basic_syntax(label, th_cmd, out):
    sc = StringScanner(th_cmd)
    cmd = verify.read_sexp(sc)
    if not cmd in ('thm', 'defthm'):
        out.write("Expected 'thm' or 'defthm'\n")
        return None
    e = verify.read_sexp(sc)
    if e is None:
        out.write('Missing command argument\n')
        return None
    if not isinstance(e, list) or len(e) < 1 or e[0] != label:
        out.write('Mismatched theorem labels.\n')
        return None
    record = sc.end_record()
    e2 = verify.read_sexp(sc)
    if e2 is not None:
        out.write('Extra expressions after %s command\n' % cmd)
        return None
    return record

def cmds_basic_syntax(cmds, out):
    sc = StringScanner(cmds)
    ncmds = 0
    while True:
        cmd = verify.read_sexp(sc)
        if cmd is None:
            break
        # For now, we don't allow import/export commands
        if not cmd in ('thm', 'defthm', 'var', 'tvar', 'kindbind'):
            out.write(
                "Expected 'thm', 'defthm', 'var', 'tvar', or 'kindbind'\n")
            return None
        e = verify.read_sexp(sc)
        if e is None:
            out.write('Missing command argument\n')
            return None
        if not isinstance(e, list) or len(e) < 1:
            out.write('Invalid command argument\n')
            return None
        ncmds += 1
    if ncmds == 0:
        return ''
    return sc.end_record()

class LogPage(webapp.RequestHandler):
    def get(self):
        pass

class RecentPage(webapp.RequestHandler):
    def get(self):
        # TODO: We could keep track of recent theorems added or changed without
        # having to do the query...
        out = self.response.out
        res = GHDatastoreUpdate(100)
        if res == 'wait':
            out.write("Ghilbert is unavailable now.\r\n")
            self.error(503)  # Service unavailable
            return
        # Redirect to same URL if not done updating.
        if res == 'again':
            self.redirect('/recent')
            return
        gen = gh_updater.current_gen
        gkey = gen.key()
        out.write("""<html><body>
<p>Recent Changes (generation %s):</p>""" % gkey.name())

        eno = gh_updater.next_entry_number
        eno -= 10
        if eno < 0:
            eno = 0

        while eno < gh_updater.next_entry_number:
            eno_keyname = number_to_key(eno)
            ekey = db.Key.from_path('GHLogEntry', eno_keyname, parent=gkey)
            entry = db.get(ekey)
            if entry is None:
                eno += 1
                continue
            ctx_ix = entry.context_index
            ctx = gh_updater.context_list[ctx_ix]
            if ctx.name is None:
                eno += 1
                continue # for now
            command = entry.command
            ctx_edit_href = ('<a href="/edit%s">%s</a>' %
                             (urllib.quote(ctx.fname), cgi.escape(ctx.fname)))
            if command == 'extend':
                verb = 'extended context %s:<br />' % ctx_edit_href
            elif command[:8] == 'replace:':
                items = command.split()
                verb = ('replaced context %s commands &lt;%s:%s&gt; :<br />' %
                        (ctx_edit_href, items[1], items[3]))
            elif command == 'new_interface_context':
                verb = ('created new interface context %s:<br />' %
                        ctx_edit_href)
            elif command.startswith('new_proof_context_named: '):
                verb = ('created new proof context %s:<br />' %
                        ctx_edit_href)
            if entry.author:
                out.write('%d. <b>%s</b> %s' %
                          (eno, entry.author.nickname(), verb))
            else:
                out.write('%d. An anonymous person %s' % (eno, verb))
            # TODO: replace thm/defthm names in content with links
            content = cgi.escape(entry.data.strip())
            newcontent = []
            for line in content.rstrip().split('\n'):
                sline = line.lstrip()
                newcontent.append('&nbsp;' * (len(line) - len(sline)) + sline)
            content = '<br />'.join(newcontent)
            out.write('<blockquote>%s</blockquote>' % content)
            eno += 1

class ReplaceHandler(webapp.RequestHandler):
    def bad_request(self, msg):
        self.error(400)
        if msg is not None:
            self.response.out.write('Replace Failed: %s\n' % msg)

    def post(self):
        
        out = self.response.out
        res = GHDatastoreUpdate(100)
        if res == 'wait':
            out.write("Ghilbert is unavailable now.\r\n")
            self.error(503)  # Service unavailable
            return
        if res == 'again':
            out.write("again\r\n")
            return

        name = self.request.get('name')
        ctxname = self.request.get('context')
        content = self.request.get('content')
        if name == '' or ctxname == '':
            self.bad_request()
            return

        logging.info("ReplaceHandler: context %s theorem %s" % (ctxname, name))
        ctx, auto_export = gh_updater.lookup_context(ctxname)
        if ctx is None:
            self.bad_request('Unknown context %s' % ctxname)
            return
        if auto_export or ctx.name is None:
            self.bad_request('%s is not a proof-file context' % ctxname)
            return

        # preferentially replace bad thms to good ones...
        bad_cmds = ctx.badthms.get(name)
        if bad_cmds is None:
            sym = ctx.syms.get(name, None)
            if sym is None:
                self.bad_request('%s not known' % name)
                return
            if sym[0] in ('var', 'tvar'):
                self.bad_request('%s is a variable, not a theorem' % name)
                return
            if sym[0] == 'stmt':
                self.bad_request('%s is an imported statement\n' % name)
                return
            cmd_ix = sym[7]
            bad = False
        else:
            cmd_ix = bad_cmds[-1] # hmm, we try to keep at most one
            bad = True

        # Probably want to make it more difficult to delete a good (verified)
        # theorem than a bad (unverified) theorem.  For now though, we
        # just do what the user asks.

        assert ((0 <= cmd_ix < len(ctx.cmd_hist)) and (cmd_ix & 3) == 0)
        cmd_ix /= 4

        record = cmds_basic_syntax(content, out)
        if record is None:
            self.bad_request('Bad command syntax')
            return

        res = gh_updater.ctx_cmds_replace(ctx.context_index,
                                          cmd_ix, cmd_ix + 1, record)
        if res:
            gh_updater.read_datastore(out)
            out.write('Replaced %s\n' % name)
        else:
            out.write('Log extension failed. Please try again.\r\n')
        return
        

class SaveHandler(webapp.RequestHandler):
    def post(self):
        global gh_updater
        global gh_base_dir

        out = self.response.out

        res = GHDatastoreUpdate(100)
        if res == 'wait':
            out.write("Ghilbert is unavailable now.\r\n")
            self.error(503)  # Service unavailable
            return
        if res == 'again':
            out.write("again\r\n")
            return

        # Note, the following line gets the un-url-encoded name.
        name = self.request.get('name')
        ctxname = self.request.get('context')
        cmd = self.request.get('content')
        cmd = cmd.strip()
        if name == '' or ctxname == '' or cmd == '':
            self.error(400) # bad request
            return
        
        logging.info("SaveHandler: context %s theorem %s" % (ctxname, name))
        ctx, auto_export = gh_updater.lookup_context(ctxname)
        if ctx is None:
            self.error(404)
            out.write('Save Failed: Unknown context %s\n' % ctxname)
            return
        if auto_export or ctx.name is None:
            self.error(404)
            out.write('Save Failed: %s is not a proof-file context\n' %
                      ctxname)
            return

        sym = ctx.syms.get(name, None)
        if sym is not None:
            if sym[0] in ('var', 'tvar'):
                out.write('Save Failed: there is a variable of name %s\n' %
                          name)
                return
            out.write(
                "Save Failed: Use 'replace' to replace existing theorem %s\n"
                % name)
            return  # TODO

        bad_cmds = ctx.badthms.get(name)
        if bad_cmds is not None:
            out.write(
                "Save Failed: Use 'replace' to replace unverified theorem %s\n"
                % name)
            return

        # FIXME: What if there is a FAILED theorem of the same name?
        # Presently it would not be replaced, but a new version would be
        # appended. Not what we want.

        # Check to see if the symbol already exists in any of the other
        # verify contexts that import ctx
        for importer in self.context_list:
            if importer.fname not in ctx.importers:
                continue
            sym = importer.syms.get(name, None)
            if sym is None:
                continue
            out.write("Save Failed: dependent context %s already contains a symbol '%s'" % (importer.name, name))
            return

        # Check the basic syntax of the 'thm' or 'defthm' command, strip
        # any trailing comments/whitespace. Does not check that the theorem
        # verifies!
        record = theorem_basic_syntax(name, cmd, out)
        if record is None:
            self.error(400)
            out.write("Save Failed: Bad syntax\n")
            return

        # Extend the datastore log with the new record consisting of the
        # thm/defthm command.
        prefix = '\n\n'
        res = gh_updater.ctx_cmds_add(ctx.context_index, prefix + record)
        if res:
            gh_updater.read_datastore(out)
            out.write('Saved %s\n' % name)
        else:
            out.write('Log extension failed. Please try again.\r\n')
        return

class ContextHandler(webapp.RequestHandler):
    def get(self, name):
        global gh_updater
        global gh_base_dir

        out = self.response.out
        # We don't perform an update here, unless gh_updater doesn't
        # exist at all. Frequently several
        # ContextHandler requests are performed at once, and
        # performing an update for each one would slow things down
        # more than we want. Other pages (e.g. the edit page) that
        # generate requests for multiple contexts should do one update
        # themselves.
        if gh_updater is None:
            res = GHDatastoreUpdate(100)
            if res == 'wait':
                out.write("Ghilbert is unavailable now.\r\n")
                self.error(503)  # Service unavailable
                return
            # Redirect to same URL if not done updating.
            if res == 'again':
                self.redirect(name)
                return

        # name here is URL-encoded, we want to display the unencoded version
        # as text, and avoid the possibility of injection attack.
        name = urllib.unquote(name);
        export = False
        ictx = None
        vctx = None
        full_pname = name
        logging.info('Looking for %s' % full_pname)
        ctx, auto_export = gh_updater.lookup_context(full_pname)
        if ctx is None:
            self.error(404)
            return

        self.response.headers['Content-Type'] = 'text/plain; charset=utf-8'
        out = self.response.out

        # We can use the command history directly for all cases except
        # for the automatically generated interface file corresponding to
        # a proof file context.
        if not auto_export:
            ix = 0
            cmd_hist = ctx.cmd_hist
            while ix < len(cmd_hist):
                cmd_text = cmd_hist[ix + 2]
                out.write(cmd_text)
                ix += 4
            return

        out.write("# Ghilbert interface file for context %s\n\n" % ctx.name)
        
        # Although we might like a 'unified' export that is all-in-one
        # without any param dependencies, some of the terms & stmts, coming
        # from imports of the proof file context ctx, may use variable
        # definitions that are not native to the ctx, and could in principle
        # be inconsistent with the variable definitions of ctx.
        # We don't have this problem if we don't do a unified export, and
        # only export the terms and theorems introduced by the ctx itself
        # For now, don't try a unified export.

        ix = 0
        cmd_hist = ctx.cmd_hist
        while ix < len(cmd_hist):
            cmd = cmd_hist[ix]
            arg = cmd_hist[ix + 1]
            undo = cmd_hist[ix + 3]
            if undo is None or isinstance(undo, verify.ErrorMark):
                out.write('# Failed: %s %s\n' %
                          (cmd, verify.sexp_to_string(arg)))
            elif cmd == 'thm':
                label, fvc, hyps, conc = arg[:4]
                hyps = hyps[1::2]
                narg = [label, fvc, hyps, conc]
                out.write('stmt %s\n' % verify.sexp_to_string(narg))
            elif cmd == 'defthm':
                label, kind, sig, fvc, hyps, conc = arg[:6]
                hyps = hyps[1::2]
                narg = [label, fvc, hyps, conc]
                tm = ctx.term_hist[ctx.terms[sig[0]]]
                # tm is (termname, ifindex, termix_orig,
                #        rkind, argkinds, freemap, sig)
                texp = [kind, sig]
                freemap = tm[5]
                for fmix in xrange(len(freemap)):
                    bmap = freemap[fmix]
                    if bmap <= 0:
                        continue  # skip non-binding and fully-bound arguments
                    bvar = sig[1 + fmix]
                    fmitem = [bvar]
                    jx = 0
                    po2 = 1
                    while po2 <= bmap:
                        if (po2 & bmap) != 0:
                            fmitem.append(sig[1 + jx])
                        jx += 1
                        po2 <<= 1
                    texp.append(fmitem)
                out.write('\nterm %s\n' % verify.sexp_to_string(texp))
                out.write('stmt %s\n' % verify.sexp_to_string(narg))
            elif cmd == 'import':
                out.write('param %s\n' % verify.sexp_to_string(arg))
            elif cmd == 'export':
                # One difficulty is that an export command in a proof file can
                # establish an interface that can be passed as an argument
                # to a subsequent import command. But if the auto-export does
                # not represent this export command, and does represent the
                # subsequent import that depends upon the export command,
                # then the auto-export will contain an invalid import
                # referring to an unknown intterface.
                # For now, we just don't support this kind of construction.
                out.write('# Unsupported: export %s' %
                          verify.sexp_to_string(arg))
            else:  # var, kindbind
                cmd_text = cmd_hist[ix + 2]
                out.write(cmd_text + '\n')
            ix += 4

        return
    
class EditPage(webapp.RequestHandler):
    def get(self, name):
        global gh_updater
        global gh_base_dir
        # name here is URL-encoded, we want to display the unencoded version
        # as text, and avoid the possibility of injection attack.

        out = self.response.out
        res = GHDatastoreUpdate(100)
        if res == 'wait':
            out.write("Ghilbert is unavailable now.\r\n")
            self.error(503)  # Service unavailable
            return
        # Redirect to same URL if not done updating.
        if res == 'again':
            self.redirect('/edit' + name)
            return

        name = urllib.unquote(name)
        if len(name) < 2 or name[0] != '/':
            self.error(404)
            return
        gh_ctx, auto_export = gh_updater.lookup_context(name)
        if gh_ctx is None:
            ps = os.path.split(name)
            gh_ctx, auto_export = gh_updater.lookup_context(ps[0])
            if gh_ctx is None:
                self.error(404)
                out.write('Not found: %s' % name)
                return
        else:
            ps = (name, '')

        # only allow proof file contexts, for now
        if gh_ctx.name is None or auto_export:
            self.error(404)
            out.write('Not a proof file context: %s' % name)
            return
        thmname = ps[1]
        existing_thm = ''
        if thmname == '':
            thmname = 'New theorem'
            cmd = None
        else:
            if thmname == 'LAST': # Get latest theorem
                hist = gh_ctx.cmd_hist
                n = len(hist)
                thmname = None
                while n >= 4:
                    n -= 4
                    cmd = hist[n]
                    if cmd not in ('thm', 'defthm'):
                        continue
                    arg = hist[n + 1]
                    if not isinstance(arg[0], basestring):
                        continue
                    thmname = arg[0]
                    break
                if thmname is None:
                    self.error(404)
                    out.write('No recognizable theorems!')
                    return
            thm = gh_ctx.syms.get(thmname, None)
            if thm is None:
                badcmdl = gh_ctx.badthms.get(thmname)
                if badcmdl is None:
                    cmd = "# No theorem named '%s' was found." % thmname
                else:
                    cmd_ix = badcmdl[0]
                    cmd = gh_ctx.cmd_hist[cmd_ix + 2].lstrip()
                    existing_thm = thmname
            elif thm[0] not in ('thm', 'defthm'):
                cmd = "# '%s' is a %s, not a theorem." % (thmname, thm[0])
            else:
                cmd_ix = thm[7]
                cmd = gh_ctx.cmd_hist[cmd_ix + 2].lstrip()
                existing_thm = thmname

        self.response.out.write("""<head><title>Ghilbert</title><style type="text/css"></style></head>

<body>
<a href="/">Home</a> <a href="/recent">Recent</a>
<h1>Ghilbert - editing <em id="thmname"></em></h1>

<script src="/js/verify.js" type="text/javascript"></script>
<script src="/js/sandbox.js" type="text/javascript"></script>
<script src="/js/inputlayer.js" type="text/javascript"></script>
<script src="/js/edit.js" type="text/javascript"></script>
<script src="/js/direct.js" type="text/javascript"></script>
<script src="/js/panel.js" type="text/javascript"></script>
<script src="/js/typeset.js" type="text/javascript"></script>

<p>
<div style="display:block;float:left">
  <label for="exist_thm">Existing theorem name: </label><input type="text" id="exist_thm" value="%s"/>
  <input type="button" id="fetch" onclick="GH.fetch(document.getElementById('exist_thm').value)" name="fetch" value="fetch"/>
  <input type="button" id="save" onclick="GH.save(document.getElementById('canvas').value)" name="save" value="save new"/>
  <input type="button" id="replace" onclick="GH.replace(document.getElementById('exist_thm').value, document.getElementById('canvas').value)" name="replace" value="replace"/><br/>
  <textarea id="canvas" cols="80" rows="20" width="640" height="480" tabindex="0"></textarea><br/>
  <canvas id="stack" width="660" height="240" tabindex="0" style="border:1px solid black"></canvas><br/>
<div id="output">(output goes here)</div>
</div>
<div width="400" height="800" style="display:block;float:left">
  <button id="inferences">Inference</button>
  <button id="deductions">Deduction</button>
  <button id="unified">Unified</button>
  <br/>
  <table id="panel" border="1" style="border:1px solid;">
  </table>
</div>
<script type="text/javascript">

name = %s;
GH.Direct.replace_thmname(name);

url = %s;
uc = new GH.XhrUrlCtx('/ctx', '/ctx' + url);
v = new GH.VerifyCtx(uc, run);
v.drop_thm(document.getElementById('exist_thm').value)
run(uc, url, v);
var mainpanel = new GH.TextareaEdit(document.getElementById('canvas'));
window.direct = new GH.Direct(mainpanel, document.getElementById('stack'));
window.direct.vg = v;
var exist_thm = document.getElementById('exist_thm');
GH.fetch = function(thmname) {
    thmname = thmname.replace(/^\s*(\S*)[\s\S]*$/, '$1');
    if (thmname.length === 0) {
        return;
    }
    document.location.href = "/edit" + url + "/" + encodeURIComponent(thmname);
};
var panel = new GH.Panel(window.direct.vg);
""" % (existing_thm, `thmname`, `ps[0]`))
## """ % (number, `name`, number));

        if cmd:
            result = json_dumps(cmd.split('\n'))
            self.response.out.write('mainpanel.setLines(%s);\n' % result)
        self.response.out.write('</script>\n')

from google.appengine.ext import webapp
import os

class PrintEnvironmentHandler(webapp.RequestHandler):
    def get(self, arg):
        self.response.out.write(json.dumps([1, 2]) + "\n")
        if arg is not None:
            print 'arg = ' + arg + '<br />\n'
        for name in os.environ.keys():
            self.response.out.write("%s = %s<br />\n" % (name, os.environ[name]))

class StaticPage(webapp.RequestHandler):
    def get(self, filename):
        try:
            lines = open('peano/%s' % filename)
        except IOError, x:
            self.error(404)
            return
        self.response.headers['Content-Type'] = 'text/plain; charset=utf-8'
        for line in lines:
            self.response.out.write(line)

class MainPage(webapp.RequestHandler):
    def get(self):
        out = self.response.out

        res = GHDatastoreUpdate(100)
        # Redirect to same URL if not done updating.
        if res == 'again':
            self.redirect('/')
            return

        out.write("""<title>Ghilbert Web Application</title>
<body>
<h1>Ghilbert web app</h1>

<p>This is an early prototype of a web app for developing
<a href="http://sites.ghilbert.org/">Ghilbert</a>
proofs.</p>

<p>See above link for basic documentation. Source code for this site
is hosted at <a href="http://ghilbert.googlecode.com/">Google Code</a>.</p>

<p><a href="/recent">Recent saves</a></p>
""")
        user = users.get_current_user()
        word = 'login'
        if user:
            word = 'logout'
            out.write('<p>Logged in as ' + user.nickname() + '\n')
            if users.is_current_user_admin():
                out.write('<p>You are an administrator.\n')
                
        out.write('<p><a href="%s">%s</a>' %
                                (users.create_login_url('/'), word))
        out.write('<p>Contexts:\n')
        if gh_updater is None:
            out.write('</body>\n')
            return
        for ctx in gh_updater.context_list:
            pfn = ctx.fname
            if ctx.name is not None:
                out.write('<p><a href="%s">%s</a> <a href="%s"> edit</a>\n' %
                          (urllib.quote('/ctx' + pfn), cgi.escape(pfn),
                           urllib.quote('/edit' + pfn)))
                pfn += 'i'
            out.write('<p><a href="%s">%s</a>\n' %
                      (urllib.quote('/ctx' + pfn), cgi.escape(pfn)))
                
        out.write('</body>\n')

class UpdateHandler(webapp.RequestHandler):
    def post(self):
        out = self.response.out
        self.response.headers['Content-Type'] = 'text/plain; charset=utf-8'
        res = GHDatastoreUpdate(100)
        out.write('%s\r\n' % res)

class ResetPage(webapp.RequestHandler):
    def get(self):
        out = self.response.out
        if not users.is_current_user_admin():
            self.error(401)
            self.response.headers['Content-Type'] = 'text/plain; charset=utf-8'
            out.write('401 Unauthorized.')
            return
        gens = all_generations()
        next_gen = next_generation(gens)
        out.write("""<title>Reset to Factory Defaults</title>
        
<body style="background-color:black;color:yellow">
<h1>Administrative Maintenance</h1>
<p>
<a href="/">Go Home</a>
<br>
<br> <label for="step_num" id="step_label"> </label>
<br> <label for="gen_entry" id="gen_entry_label"> Generation </label> <input type="text" id="gen_entry" name="gen" size="16" tabindex="0" value="%s"/>
<input type="button" id="init" style="background-color:yellow;color:black;" onclick="factory_reset('init')" name="init" value="Create with Default Content"/>
<input type="button" id="clear" style="background-color:red;color:black;" onclick="factory_reset('clear')" name="reset" value="Clear"/>
<br/>
<script type="text/javascript">
factory_reset = function (cmd) {
    var req = new XMLHttpRequest();
    req.open('POST', '/reset', true);
    var oldresp = null
    var label = document.getElementById('step_label');
    var gen_entry = document.getElementById('gen_entry');
    var body = 'cmd=' + cmd + '&gen=' + encodeURIComponent(gen_entry.value);
    var rsc_func = function () {
        if (req.readyState != 4) {
            return;
        }
        var resp = req.responseText;
        if (req.status != 200) {
            label.innerHTML += ' ERROR: ' + req.status + ' ' + resp;
            req.abort()
            req = null
            return
        }
        if (resp.substring(0, 4) === 'done') {
            req = null
            window.location.href = '/reset'
            return
        } else if (resp === oldresp) {
            label.innerHTML += '.';
        } else {
            label.innerHTML = resp;
            oldresp = resp
        }
        req.open('POST', '/reset', true);
        req.setRequestHeader('Content-Type',
                             'application/x-www-form-urlencoded');
        req.onreadystatechange = rsc_func;
        req.send(body);
    };
    req.onreadystatechange = rsc_func;
    req.setRequestHeader('Content-Type', 'application/x-www-form-urlencoded');
    label.innerHTML = '';
    req.send(body);
};

</script>
""" % str(next_gen))
        out.write('<br>Generations:')
        for n in gens:
            out.write(' %d' % n)
        out.write('</body>\n')
        return

    def genstr_to_num(self, gen):
        try:
            n = long(gen)
        except ValueError:
            self.error(400)
            self.response.out.write('Bad generation: ' + gen)
            return -1
        if n <= 0 or n > 0x7fffffffffffffff:
            self.error(400)
            self.response.out.write('Generation out of range: ' + gen)
            return -1
        return n

    def post(self):
        out = self.response.out
        self.response.headers['Content-Type'] = 'text/plain; charset=utf-8'
        if not users.is_current_user_admin():
            self.error(401)
            out.write('401 Unauthorized.')
            return
        cmd = self.request.get('cmd')
        gen = self.request.get('gen')
        #logging.info("ResetPage post cmd='%s', gen='%s'" % (cmd, gen))
        if cmd == 'clear':
            if gen == 'all':
                if clear_datastore(80):
                    out.write('done')
                else:
                    out.write('Clearing...')
                return
            n = self.genstr_to_num(gen)
            if n < 0:
                return
            if clear_generation(n, 80):
                out.write('done')
            else:
                out.write('Clearing...')
            return
        if cmd != 'init':
            self.error(400)
            out.write('Unknown command.')
            return

        n = self.genstr_to_num(gen)
        if n < 0:
            return
        defaults = [
            [None,          u'/peano/prop_ax.ghi'],
            [u'PROP',       u'/peano/prop.gh'],
            [None,          u'/peano/pred_ax.ghi'],
            [u'PRED',       u'/peano/pred.gh'],
            [None,          u'/peano/peano_ax.ghi'],
            [u'PEANO',      u'/peano/peano_thms.gh'],
            [None,          u'/peano/naive_set.ghi'],
            [u'PEANO_SET',  u'/peano/peano_set.gh'],
            ]
        res = GHGenerationCreate(n, defaults)
        if res == 'conflict':
            self.error(400)
        out.write(res)
        return
                

application = webapp.WSGIApplication(
                                     [('/', MainPage),
                                      ('/recent', RecentPage),
                                     # ('/peano/(.*)', StaticPage),
                                      ('/edit(.*)', EditPage),
                                      ('/env(/.*)?', PrintEnvironmentHandler),
                                      ('/ctx(.*)', ContextHandler),
                                      ('/save', SaveHandler),
                                      ('/replace', ReplaceHandler),
                                      ('/reset', ResetPage),
                                      ('/update', UpdateHandler),
                                      ('/log', LogPage),
                                      ], debug=True)

gh_base_dir = os.path.realpath(os.getcwd())  # realpath not necessary?

def main():
    run_wsgi_app(application)

if __name__ == "__main__":
    main()
