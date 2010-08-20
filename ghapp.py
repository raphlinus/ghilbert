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

from django.utils import simplejson

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
    def __init__(self, str_to_scan):
        if isinstance(str_to_scan, str):
            self.record = str_to_scan
        else:
            self.record = str_to_scan.encode('ascii')
        self.record = self.record.strip()
        self.lines = self.record.splitlines()
        self.lineno = 0
        self.toks = []
        self.tokix = 0

    def get_tok(self):
        while len(self.toks) == self.tokix:
            if self.lineno >= len(self.lines):
                return None
            line = self.lines[self.lineno]
            self.lineno += 1
            line = line.split('#')[0]
            line = line.replace('(', ' ( ')
            line = line.replace(')', ' ) ')
            self.toks = line.split()
            self.tokix = 0
        result = self.toks[self.tokix]
        self.tokix += 1
        return result

# The low-order 32 bits of EditGeneration() increments whenever there
# is a database change that extends (but does not invalidate) earlier
# work.  The high-order 32 bits of EditGeneration() increments whenever
# there is a change that requires a full re-read of the datastore.
# There will be just one entity of this kind in the database.
# All items in the database have EditGeneration as parent.
class EditGeneration(db.Model):
    gen = db.IntegerProperty()

# Can the EditGeneration idea be race-free?

class GHContext(db.Model):
    name = db.StringProperty()  # will be None for interface file
    fname = db.StringProperty(required=True) # use TextProperty() instead?
    level = db.IntegerProperty(required=True)

# Represents an import/param/export command
class GHInterface(db.Model):
    ctx_from = db.ReferenceProperty(GHContext,
                                    collection_name="ghinterface_from_set",
                                    required=True)
    ctx_to = db.ReferenceProperty(GHContext,
                                  collection_name="ghinterface_to_set",
                                  required=True)
    # 'name' names this import among all imports of the parent interface
    name = db.StringProperty(required=True)
    prefix = db.StringProperty()
    params = db.TextProperty()
    # index among interfaces with the same ctx_from
    index = db.IntegerProperty(required=True)
    style = db.StringProperty(required=True,
                              choices=set(['param', 'import', 'export']))

class GHKind(db.Model):
    ctx = db.ReferenceProperty(GHContext, required=True)
    name = db.StringProperty(required=True)

class GHKindbind(db.Model):
    ctx = db.ReferenceProperty(GHContext, required=True)
    k_old = db.StringProperty(required=True)
    k_new = db.StringProperty(required=True)

class GHVar(db.Model):
    ctx = db.ReferenceProperty(GHContext, required=True)
    name = db.StringProperty(required=True)
    var_kind = db.StringProperty(required=True)
    binding = db.BooleanProperty(default=False)

class GHTerm(db.Model):
    ctx = db.ReferenceProperty(GHContext, required=True)
    arg = db.TextProperty(required=True)
    
class GHStmt(db.Model):
    ctx = db.ReferenceProperty(GHContext, required=True)
    cmd = db.TextProperty(required=True)

# Note, we don't order the theorems in the database. We infer an ordering
# that works (when possible).
# We don't want to store any index or depth value to order the theorems,
# since such a value would have to be recalculated for a large number of
# theorems if a theorem were inserted earlier, or a proof of an existing
# theorem changes in depth.
class GHThm(db.Model):
    ctx = db.ReferenceProperty(GHContext, required=True)
    name = db.StringProperty(required=True)
    cmd = db.TextProperty(required=True)
    author = db.UserProperty()
    date = db.DateTimeProperty(auto_now=True)

# Use cases:
# - Retrieve all kinds, terms, variables, and statements valid (axiomatic or
#   provable) in a context.
# - Retrieve just those statements and terms that are axiomatic in a context.
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

# (Current generation number, EditGeneration object)
gh_edit_gen = (0, None)

def clear_datastore(maxitems=0):
    logging.warning('***** Clearing Datastore! *****')
    # We wanted to just clear everything, i.e.
    #   q = db.Query()
    #   for item in q:
    #      item.delete()
    # but got errors in the production app-engine when
    # this apparently tried to delete some internal entities.
    # Then we tried restricting to clearing all descendents of
    # a particular ancestor_key, but during development several
    # different ancestor keys (and sometimes none at all) got used,
    # and wouldn't get deleted.
    # So for robustness, we instead clear all kinds that this
    # app uses.
##    q = db.Query()
##    q.ancestor(ancestor_key)
##    items = 0
##    for item in q:
##        item.delete()
##        items += 1
##        if maxitems != 0 and items >= maxitems:
##            return False

    items = 0
    classes = (GHThm, GHStmt, GHVar, GHTerm, GHInterface, GHKind, GHKindbind, GHContext, EditGeneration)
    for cl in classes:
        q = cl.all()
        for item in q:
            item.delete()
            items += 1
            if maxitems != 0 and items >= maxitems:
                return False
    
    return True

gh_dsinit = None

def GHDatastoreReset(ancestor_key, defaults, maxitems):
    while True:
        done = clear_datastore(2 * maxitems)
        if done:
            break
        yield 'Clearing'
    ghdi = GHDatastoreInitializer(maxitems)
    for name, path in defaults:
        acp = ghdi.add_context_partial(name, path)
        for done in acp:
            if isinstance(acp, basestring):
                yield done
            else:
                yield path

class GHDatastoreInitializer(object):
    def __init__(self, maxitems):
        self.ds_contexts = {}
        self.gctx = verify.GlobalCtx()
        self.out = DummyWriter()
        self.maxitems = maxitems
        self.count = 0

    def yield_now(self):
        self.count += 1
        if self.count >= self.maxitems:
            self.count = 0
            return True
        return False

    def add_context_partial(self, name, path):
        global gh_base_dir

        if path in self.ds_contexts:
            logging.error("Verify context %s (%s) repeated." % (name, path))
            return

        logging.info("Adding context %s, from %s" % (name, path))

        def ghapp_build_if(ctx, fn, url):
            global gh_base_dir
            global_ctx = ctx.global_ctx
##          logging.info(
##                'ghapp_build_if: fn=%s ctx.global_ctx.all_interfaces=%r'
##                % (fn, global_ctx.all_interfaces))
            if not fn.startswith(gh_base_dir):
                logging.error(
                    'ghapp_build_if: interface path %s does not start with %s'
                    % (fn, gh_base_dir))
                raise verify.VerifyError('Bad path prefix')
            if fn.endswith('.ghi'):
                fnp = fn[:-1]
                vctx = global_ctx.all_interfaces.get(fnp, None)
                if vctx is not None:
                    if fnp in global_ctx.iface_in_progress:
                        raise verify.VerifyError(
                            "Tried to fetch auto-export of in-progress %s" % fnp)
                    if vctx.name is not None:
                        #logging.info("ghapp_build_if: using verify context for %s" % fn)
                        return vctx

            # Note, the fetch_interface() checked global_ctx.all_interfaces
            # for a match before this routine was called. Create a new interface.
            pif = verify.InterfaceCtx(ctx.urlctx, ctx.run, global_ctx, fn,
                                      ctx.build_interface)
            pif.record = ctx.record
            if not pif.run(ctx.urlctx, url, pif):
                raise verify.VerifyError(
                    "Failed while loading interface '%s'" % url)
            pif.complete()
            return pif

        # TODO: rethink the filename / path handling here
        urlctx = verify.UrlCtx(gh_base_dir, path, None, False)
        path_norm = urlctx.normalize(path)
        vctx = verify.VerifyCtx(urlctx, verify.run, self.gctx, path_norm,
                                ghapp_build_if, False)

        vctx.name = name
        vctx.out = self.out
        vctx.verbosity = 0
        vctx.record = ''
        vctx.ignore_exports = True
        vctx.run(urlctx, path, vctx)
        if vctx.error_count != 0:
            logging.warning('%d errors verifying %s' % (vctx.error_count,
                                                          name))
        vctx.complete()

        for done in self.init_datastore_ictx(vctx, name):
            yield done

    def init_datastore_ictx(self, gh_ctx, name=None):
        global gh_base_dir
        global gh_edit_gen

        fname = gh_ctx.fname
        if not fname.startswith(gh_base_dir):
            logging.error('Real interface path %s does not start with %s' %
                          (fname, gh_base_dir))
            raise verify.VerifyError('Bad path prefix')
        fname = fname[len(gh_base_dir):]

        if fname in self.ds_contexts:
            logging.info("Context %s (%s) repeated." % (name, fname))
            yield self.ds_contexts[fname]
            return

        logging.info("Building Ghilbert context %s" % fname)

        ds_ctx = GHContext(name=name, fname=fname, level=gh_ctx.level,
                           parent=gh_edit_gen[1])
        ds_ctx.put()
        self.ds_contexts[fname] = ds_ctx

        if self.yield_now():
            yield fname

        # First, all the imports.

        for ix in xrange(len(gh_ctx.iflist)):
            imp = gh_ctx.iflist[ix]
            # For verify context,
            #  ifname, ictx, params, prefix, kindmap, termmap, style
            # termmap and style are absent for an interface file context.
            ifname, ictx, params, prefix = imp[:4]
            # We only handle imports that occur before any export, in order
            # that we can put them all at the start of the file.
            # We generate exported interface files automatically, so we don't
            # store their results separately in the datastore.
            if name is not None:
                if imp[6] == 'export':
                    break
                style = 'import'
            else:
                style = 'param'
            param_fname = ictx.fname
            try:
                ids_ctx = self.ds_contexts[param_fname]
            except KeyError:
                igen = self.init_datastore_ictx(ictx, None)
                for done in igen:
                    ids_ctx = done  # last item returned is imported context
                    if isinstance(done, basestring):
                        yield done

            pnames = [gh_ctx.iflist[jx][0] for jx in params]
            paramnames = '#'.join(pnames)
            iface = GHInterface(ctx_from=ds_ctx, ctx_to=ids_ctx, name=ifname,
                                prefix=prefix, params=paramnames, index=ix,
                                style='import',
                                parent=gh_edit_gen[1])
            iface.put()
            if self.yield_now():
                yield fname

        # Kinds
        if name is None:
            for kh in gh_ctx.kind_hist:
                kname, ifindex, kix = kh
                if ifindex >= 0:
                    continue        # skip kinds originating elsewhere
                ghk = GHKind(ctx=ds_ctx, name=kname,
                             parent=gh_edit_gen[1])
                ghk.put()
                if self.yield_now():
                    yield fname

        # Kindbinds. We allow kindbind (with alias-only semantics) in interface
        # files as well as proof files.
        for k in gh_ctx.kindbinds:
            kix = gh_ctx.kinds[k]
            kv = gh_ctx.kind_hist[kix]
            ghkb = GHKindbind(ctx=ds_ctx, k_old=kv[0], k_new=k,
                              parent=gh_edit_gen[1])
            ghkb.put()
            if self.yield_now():
                yield fname

        # Variables.  Ugh, two passes through this...
        for vname, sym in gh_ctx.syms.iteritems():
            if sym[0] != 'var' and sym[0] != 'tvar':
                continue
            #logging.info('vname=%s, sym=%r' % (vname, sym))
            if len(sym) == 4:
                kname = sym[3]
            else:
                kname = gh_ctx.kind_hist[sym[1]][0]
            ghv = GHVar(ctx=ds_ctx, name=vname, var_kind=kname,
                        binding=(sym[0] == 'var'),
                        parent=gh_edit_gen[1])
            ghv.put()
            if self.yield_now():
                yield fname

        if name is not None:
            # Now, all the verify context's thm's and defthm's.
            for ah in gh_ctx.assertion_hist:
                # logging.info('creating [def]thm entity: %s' % ah)
                thm = gh_ctx.syms[ah]
                # thm is (kw, fv, hyps, concl, varlist,
                #         num_hypvars, num_nondummies, record)
                ght = GHThm(ctx=ds_ctx, name=ah, cmd=thm[7],
                            parent=gh_edit_gen[1])
                ght.put()
                if self.yield_now():
                    yield fname
                #logging.info('put %s' % ah)

            logging.info("Finished Ghilbert context %s" % fname)
            yield ds_ctx
            return  # No terms/stmts in verify context except defthm terms

        # Terms (other than defthm terms in verify context)
        for th in gh_ctx.term_hist:
            tname, ifindex, termix, rkind, argkinds, freemap, sig = th
            if ifindex >= 0:
                continue        # skip terms originating elsewhere
            arg = gh_ctx.term_arg_string(rkind, sig, freemap)
            ght = GHTerm(ctx=ds_ctx, arg=arg,
                         parent=gh_edit_gen[1])
            ght.put()
            if self.yield_now():
                yield fname

        # stmt's
        for ah in gh_ctx.assertion_hist:
            stmt = gh_ctx.syms[ah]
            #logging.info('creating stmt entity: %s %r' %
            #             (ah, stmt))
            # stmt is (kw, fv, hyps, concl, varlist,
            #          num_hypvars, num_nondummies, record)
            ghs = GHStmt(ctx=ds_ctx, cmd=stmt[7],
                         parent=gh_edit_gen[1])
            ghs.put()
            if self.yield_now():
                yield fname

        logging.info("Finished Ghilbert context %s" % fname)
        yield ds_ctx
        return

# gh_global_ctx will be a verify.GlobalCtx.
gh_global_ctx = None

class DummyWriter(object):
    def __init__(self):
        pass
    def write(self, data):
        logging.info('%s' % data)
        return

dummy_writer = DummyWriter()

class GHDatastoreError(Exception):
    def __init__(self, why):
        self.why = why

def gh_edit_gen_refresh():
    global gh_edit_gen
    _, egen = gh_edit_gen
    if egen is None:
        egen_q = EditGeneration.all()
        for e in egen_q:
            egen = e
            break
    if egen is None:
        return 0
    egen = db.get(egen.key())
    if egen is None:
        return 0
    edit_gen = egen.gen
    gh_edit_gen = (edit_gen, egen)
    return edit_gen
    
gh_updater = None

def GHDatastoreUpdate(maxitems):
    """ Attempt to (partially) update the verifier datastructures based
        upon the current datastore contents.
        - Returns 'done' if the verifier datastructures were brought up to
          the current state (however briefly)
        - Returns 'again' if the verifier datastructures are not yet up to
          current. Client should call again.
        - Returns 'wait' if the datastore is currently empty or being
          reinitialized
    """
    global gh_edit_gen
    global gh_updater

    if gh_updater is None:
        edit_gen, egen = gh_edit_gen
        edit_gen_now = gh_edit_gen_refresh()
        if edit_gen_now == 0:
            return 'wait'
        if edit_gen_now == edit_gen:
            return 'done'
        gh_updater = GHUpdater(maxitems, edit_gen_now)
    try:
        gh_updater.generator.next()
    except StopIteration:
        egi = gh_updater.edit_gen_init
        gh_updater = None
        edit_gen_now = gh_edit_gen_refresh()
        if edit_gen_now == 0:
            return 'wait'
        if edit_gen_now == egi:
            return 'done'
    # TODO: catch other exceptions?
    return 'again'
        
    

class GHUpdater(object):
    def __init__(self, maxitems, edit_gen_init):
        self.maxitems = maxitems
        self.count = 0
        self.edit_gen_init = edit_gen_init
        self.generator = self.read_datastore()

    def yield_now(self):
        self.count += 1
        if self.count >= self.maxitems:
            self.count = 0
            return True
        return False

    # TODO: must do this in pieces at repeated request from client
    # It takes too long, otherwise, for the full read case.
    def read_datastore(self):
        global gh_global_ctx
        global gh_base_dir
        global dummy_writer

        logging.info('Reading datastore')
        out = dummy_writer
        gh_global_ctx = verify.GlobalCtx()
        ctx_q = GHContext.all()
        ctx_q.order('level')
        for ds_ctx in ctx_q:
            pfname = ds_ctx.fname.encode('ascii')
            logging.info('Context: %s' % pfname)
            cname = ds_ctx.name
            full_pname = os.path.join(gh_base_dir, pfname[1:])
            if full_pname in gh_global_ctx.all_interfaces:
                raise GHDatastoreError('Duplicate context file name "%s"'
                                       % pfname)
            urlctx = verify.UrlCtx(gh_base_dir, pfname, None, False)
            if cname is not None:
                gh_ctx = verify.VerifyCtx(urlctx, None, gh_global_ctx,
                                          full_pname, False)
                gh_ctx.name = cname.encode('ascii')
                # verify contexts that import this context's automatically
                # exported interface. Indexed by full pathname.
                gh_ctx.importers = {}
            else:
                if full_pname in gh_global_ctx.iface_in_progress:
                    raise GHDatastoreError(
                     'Recursive reference to interface context %s in progress.'
                     % full_pname)
                gh_ctx = verify.InterfaceCtx(urlctx, None, gh_global_ctx,
                                             full_pname, None)
            gh_ctx.verbosity = 0
            gh_ctx.out = out
            gh_ctx.datastore_context = ds_ctx
            for done in self.read_context(ds_ctx, gh_ctx, out):
                yield done
            gh_ctx.complete()
    
    def read_context(self, ds_ctx, ictx, out):
        q = GHInterface.all()
        q.filter("ctx_from =", ds_ctx)
        q.order("index")

        # Handle all params/imports
        for iface in q:
            read_iface(iface, ictx, out)
            if self.yield_now():
                yield False

        # Handle all locally defined kinds; don't need to do this for
        # verify contexts.
        if ictx.name is None:
            for ghk in ds_ctx.ghkind_set:
                kname = ghk.name.encode('ascii')
                # check_id(kname)
                n = len(ictx.kind_hist)
                ictx.add_kind(kname, n)
                ictx.kind_hist.append((kname, -1, n))
                if self.yield_now():
                    yield False

        # We allow kindbinds (with alias-only semantics) in both interface
        # files and proof files now...
        for ghkb in ds_ctx.ghkindbind_set:
            k_old = ghkb.k_old.encode('ascii')
            # check_id(k_old)
            k_new = ghkb.k_new.encode('ascii')
            # check_id(k_new)
            #logging.info('kindbind (%s %s)' % (k_old, k_new))
            ictx.add_kind(k_new, ictx.get_kind(k_old))
            ictx.kindbinds.append(k_new)
            if self.yield_now():
                yield False

        # Variables
        for ghv in ds_ctx.ghvar_set:
            vname = ghv.name.encode('ascii')
            # check_id(vname)
            if vname in ictx.syms:
                raise verify.VerifyError(
                    "A symbol '%s' already exists in interface %s" %
                    (vname, ictx.fname))
            kname = ghv.var_kind.encode('ascii')
            # check_id(kname)
            try:
                kix = ictx.kinds[kname]
            except KeyError:
                raise verify.VerifyError(
                    "The kind '%s' does not exist in interface %s" %
                    (kname, ictx.fname))
            if ictx.name is None:
                ictx.syms[vname] = (('var' if ghv.binding else 'tvar'), kix, vname)
            else:
                ictx.syms[vname] = (('var' if ghv.binding else 'tvar'), kix,
                                    vname, kname)
            #logging.info("Variable: (%s %d %s)\n" % ictx.syms[vname])
            if self.yield_now():
                yield False


        # Terms, statements for interface contexts
        if ictx.name is None:
            for ght in ds_ctx.ghterm_set:
                # logging.info('term arg: %s' % ght.arg)
                sc = StringScanner(ght.arg)
                ictx.scanner = sc
                e = verify.read_sexp(sc)
                if e is None:
                    raise verify.VerifyError("Unexpected end of data -- term.")
                try:
                    ictx.do_cmd('term', e, None)
                except verify.VerifyError, x:
                    logging.error('%s' % x.why)
                    raise
                if self.yield_now():
                    yield False

            for ghs in ds_ctx.ghstmt_set:
                sc = StringScanner(ghs.cmd)
                ictx.scanner = sc
                # logging.info('stmt cmd: %s' % sc.record)
                cmd = verify.read_sexp(sc)
                if cmd != 'stmt':
                    raise verify.VerifyError("Expected stmt command")
                e = verify.read_sexp(sc)
                if e is None:
                    raise verify.VerifyError("Unexpected end of data -- stmt.")
                try:
                    ictx.do_cmd('stmt', e, sc.record)
                except verify.VerifyError, x:
                    logging.error('%s' % x.why)
                    raise
                if self.yield_now():
                    yield False

        if ictx.name is not None:
            ictx.bad_thms = []
            ictx.unresolved_thms = {}
            for ghth in ds_ctx.ghthm_set:
                # handle out-of-order cases
                add_thm(ictx, ghth.name.encode('ascii'), ghth.cmd, True)
                if self.yield_now():
                    yield False
            logging.info('There are %s bad and %s unresolved theorems' %
                         (len(ictx.bad_thms), len(ictx.unresolved_thms)))

def read_iface(iface, ictx, out):
    global gh_global_ctx
    global gh_base_dir

    fname = iface.ctx_to.fname.encode('ascii')
    # check_id(fname)
    full_pname = os.path.join(gh_base_dir, fname[1:])
    try:
        pif = gh_global_ctx.all_interfaces[full_pname]
    except KeyError:
        raise GHDatastoreError(
            'Interface %s not already loaded when needed by %s'  %
            (fname, ictx.fname))

    ifname = iface.name.encode('ascii')
    # check_id(ifname)
    if ifname in ictx.interfaces:
        raise verify.VerifyError(
            "An interface of name '%s' already exists in %s"
            % (ifname, ictx.fname))
    prefix = iface.prefix.encode('ascii')
    # check_id('"' + prefix + '"')
    epn = iface.params.encode('ascii')
    param_names = ([] if epn == '' else epn.split('#'))

    if ictx.name is None:
        ictx.param(ifname, pif, param_names, prefix)
    else:
        cmd = iface.style.encode('ascii')
        if cmd == 'import':
            ictx.gh_import(pif, ifname, param_names, prefix)
            if pif.name is not None:
                if ictx.fname not in pif.importers:
                    logging.info ('Setting %s as importer of %s' %
                                  (ictx.fname, full_pname))
                    pif.importers[ictx.fname] = ictx
        elif cmd == 'export': # shouldn't really occur at present...
            ictx.gh_export(pif, ifname, param_names, prefix)
        else:
            raise verify.VerifyError("Unexpected interface command %s" % cmd)

    if pif.level >= ictx.level:
        ictx.level = pif.level + 1

def find_unresolved_terms(vctx, exp, unk_terms):
    if not isinstance(exp, list):
        return
    if len(exp) < 1 or isinstance(exp[0], list):
        raise SyntaxError("Invalid term.")
    tname_tup = (exp[0],)
    if exp[0] not in vctx.terms and tname_tup not in unk_terms:
        unk_terms.append(tname_tup)
    for e in exp[1:]:
        find_unresolved_terms(vctx, e, unk_terms)

def find_unresolved(vctx, cmd, e, cmdstr):
    # thm (LABEL FVC HYPS CONC STEPS)
    # defthm (LABEL KIND SIG FVC HYPS CONC STEPS)
    # cmdstring has the full command + arg with comments
    unk = []
    unk_terms = []
    steps_ix = (4 if cmd == 'thm' else 6)
    if (not isinstance(e, list) or len(e) <= steps_ix or
        not isinstance(e[0], basestring) or
        not isinstance(e[steps_ix - 2], list) or
        (len(e[steps_ix - 2]) & 1) != 0):
        raise SyntaxError("Bad 'thm' or 'defthm' syntax.")

    hyps = e[steps_ix - 2]

    hypnames = {}
    for ix in xrange(0, len(hyps), 2):
        hn = hyps[ix]
        if not isinstance(hn, basestring):
            raise SyntaxError("Hypothesis name must be an identifier.")
        hypnames[hn] = 0 # don't really need value here...
        find_unresolved_terms(vctx, hyps[ix + 1], unk_terms)

    # recored all proof steps that are unknown identifiers
    for step in e[steps_ix:]:
        if isinstance(step, list):
            find_unresolved_terms(vctx, step, unk_terms)
            continue
        if step not in hypnames and step not in vctx.syms:
            if step not in unk:
                unk.append(step)
    # tag on the command and argument
    unk.append(cmd)
    unk.append(e)
    unk.append(cmdstr)
    return unk_terms + unk

def may_be_resolved(thmap, vctx, ul, unk):
    # deal with theorems pending waiting for the assertion or defined term
    # that just became available (and perhaps waiting for others)
    for u in ul:
        while len(u) > 3:
            if isinstance(u[0], tuple):
                if u[0][0] in vctx.terms:
                    u = u[1:]
            elif u[0] in vctx.syms:
                u = u[1:]
            else:
                break
        if len(u) == 3:  # ready to resolve u
            logging.info('resolved %s' % u[-2])
            unk.extend(u)
            continue
        if len(u) < 3:
            raise verify.VerifyError('may_be_resolved() internal error')
        logging.info('theorem %s still unresolved for %s' %
                     (u[-2][0], u[0]))
        # u still needs other theorems before it can be resolved
        try:
            ul2 = thmap[u[0]]
        except KeyError:
            ul2 = []
            thmap[u[0]] = ul2
        ul2.append(u[1:])

def add_thm(vctx, name, th_cmd, keep_if_fail):
    """ Called from both the read_datastore() and SaveHandler() code
        paths, this routine adds the theorem command th_cmd to the
        vctx verify context. If keep_if_fail is true, the theorem may
        be kept in vctx.unresolved_thms or in vctx.bad_thms if it fails
        to verify...
        Returns True if the theorem was successfully added, False otherwise.
    """
    sc = StringScanner(th_cmd)
    vctx.scanner = sc
    cmd = verify.read_sexp(sc)
    #logging.info("add_thm %s %s" % (cmd, name))
    if not cmd in ('thm', 'defthm'):
        vctx.out.write("Expected 'thm' or 'defthm'\n")
        return False
    e = verify.read_sexp(sc)
    if e is None:
        vctx.out.write('Missing command argument\n')
        return False
    if not isinstance(e, list) or len(e) < 1 or e[0] != name:
        vctx.out.write('Mismatched theorem labels.\n')
        return False
    try:
        unk = find_unresolved(vctx, cmd, e, sc.record)
    except SyntaxError, x:
        vctx.out.write('%s\n' % str(x))
        return False

##    logging.info("add %s %s, unresolved %r" %
##                 (cmd, verify.sexp_to_string(e), unk))
    thmap = vctx.unresolved_thms
    if len(unk) > 3:
        if not keep_if_fail:
            vctx.out.write("Unresolved symbol '%s'\n" % unk[0])
            return False
        logging.info("Deferring %s for unresolved %s" % (name, unk[0]))
        try:
            ul = thmap[unk[0]]
        except KeyError:
            ul = []
            thmap[unk[0]] = ul
        ul.append(unk[1:])
        return False

    while len(unk) > 0:
        # unk[:3] is [cmd, e, cmdstr] for newly resolved theorem
        cmd, e, cmdstr = unk[:3]
        unk = unk[3:]
        record = cmdstr
        # logging.info("resolved %s" % e[0])
        if cmd == 'defthm':
            if (not isinstance(e, list) or len(e) < 2 or
                not isinstance(e[2], list) or len(e[2]) < 0):
                logging.info("bad %s" % cmdstr)
                if not keep_if_fail:
                    return False
                vctx.bad_thms.append(cmdstr)
                continue
            # save both the command string and the defined term name
            record = (cmdstr, e[2][0])

        ok = True
        try:
            vctx.do_cmd(cmd, e, record)
        except verify.VerifyError, x:
            vctx.out.write('Verify error:\n%s\n' % x.why)
            ok = False
        except SyntaxError, x:
            vctx.out.write('Syntax error:\n%s\n' % str(x))
            ok = False
        if not ok:
            if not keep_if_fail:
                return False
            vctx.bad_thms.append(cmdstr)
            continue

        if cmd == 'defthm':
            # Is any theorem waiting on the until-now unresolved term?
            ul = thmap.get((record[1],), None)
            if ul != None:
                del thmap[(record[1],)]
                may_be_resolved(thmap, vctx, ul, unk)

        name = e[0]
        keep_if_fail = True
        ul = thmap.get(name, None)
        if ul is None:
            continue
        del thmap[name]
        may_be_resolved(thmap, vctx, ul, unk)

    return True


class Greeting(db.Model):
    author = db.UserProperty()
    content = db.StringProperty(multiline=True)
    date = db.DateTimeProperty(auto_now_add=True)

class RecentPage(webapp.RequestHandler):
    def get(self):
        # TODO: We could keep track of recent theorems added or changed without
        # having to do the query...
        self.response.out.write("""<html><body>
<p>Recent saves:</p>""")

        thms = db.GqlQuery("SELECT * FROM GHThm ORDER BY date DESC LIMIT 10")

        out = self.response.out
        for thm in thms:
            if thm.author:
                out.write('<b>%s</b> wrote ' % thm.author.nickname())
            else:
                out.write('An anonymous person wrote ')
            ctx = thm.ctx
            out.write('<a href="/edit%s">%s</a>:<br />' %
                      (urllib.quote(ctx.fname + '/' + thm.name),
                       cgi.escape(thm.name)))
            if (thm.cmd is None):
                content = ""
            else:
                content = cgi.escape(thm.cmd)
            newcontent = []
            for line in content.rstrip().split('\n'):
                sline = line.lstrip()
                newcontent.append('&nbsp;' * (len(line) - len(sline)) + sline)
            content = '<br />'.join(newcontent)
            out.write('<blockquote>%s</blockquote>' % content)

def datastore_add_new_thm(ctx, name, cmd):
    ds_ctx = ctx.datastore_context
    gh_thm = GHThm(ctx=ds_ctx, name=name, cmd=cmd,
                   parent=gh_edit_gen[1])
    if users.get_current_user():
        gh_thm.author = users.get_current_user()
    gh_thm.put()

def datastore_add_new_thm_cb(ctx, name, cmd, edit_gen, egen):
    datastore_add_new_thm(ctx, name, cmd)
    egen = db.get(egen.key())
    if edit_gen != egen.gen:
        raise db.Rollback("Database updated by another context while saving theorem.")
    edit_gen += 1
    egen.gen = edit_gen
    egen.put()
    return (edit_gen, egen)

def datastore_add_new_thm_transaction(ctx, name, cmd, edit_gen, egen):
    global gh_edit_gen
    res = db.run_in_transaction(datastore_add_new_thm_cb,
                                ctx, name, cmd, edit_gen, egen)
    if res is not None:
        gh_edit_gen = res
    return res

class SaveHandler(webapp.RequestHandler):
    def post(self):
        global gh_edit_gen
        global gh_global_ctx
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
        edit_gen, egen = gh_edit_gen

        # Note, the following line gets the un-url-encoded name.
        name = self.request.get('name')
        ctxname = self.request.get('context')
        cmd = self.request.get('content')
        if name == '' or ctxname == '' or cmd == '':
            self.error(400) # bad request
            return
        
        logging.info("SaveHandler: context %s theorem %s" % (ctxname, name))
        ctxname_full = os.path.join(gh_base_dir, ctxname[1:])
        try:
            ctx = gh_global_ctx.all_interfaces[ctxname_full]
        except KeyError:
            out.write('Save Failed: Unknown context %s\n' % ctxname)
            return
        if ctx.name is None:
            out.write('Save Failed: Context %s is not a proof-file context\n'
                      % ctxname)
            return

        sym = ctx.syms.get(name, None)
        if sym is not None:
            if sym[0] in ('var', 'tvar'):
                out.write('Save Failed: there is a variable of name %s\n' %
                          name)
                return
            out.write('Save Failed: Cannot replace existing theorem yet...')
            return  # TODO

        # Check to see if the symbol already exists in any of the other
        # verify contexts that import ctx
        for importer in ctx.importers.itervalues():
            sym = importer.syms.get(name, None)
            if sym is None:
                continue
            out.write("Save Failed: dependent context %s already contains a symbol '%s'" % (importer.name, name))
            return

        ctx.out = out
        result = add_thm(ctx, name, cmd, False)
        ctx.out = dummy_writer
        if result: # TODO -- save incomplete / broken theorems
            res = datastore_add_new_thm_transaction(ctx, name, cmd,
                                                    edit_gen, egen)
            if res is None:
                out.write('Save failed. Please try again.\r\n')
                return
            out.write('Saved %s\n' % name)
        else:
            out.write('Failed.\n')
        return
        
class ContextHandler(webapp.RequestHandler):
    def get(self, name):
        global gh_global_ctx
        global gh_base_dir

        out = self.response.out
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
        full_pname = os.path.join(gh_base_dir, name[1:])
        logging.info('Looking for %s' % full_pname)
        ctx = gh_global_ctx.all_interfaces.get(full_pname, None)
        if ctx is None:
            if full_pname.endswith('.ghi'):
                vctx = gh_global_ctx.all_interfaces.get(full_pname[:-1], None)
                ctx = vctx
                export = True
        elif ctx.name is None:
            ictx = ctx
        else:
            vctx = ctx
        if ictx is None and vctx is None:
            self.error(404)
            return
                
        self.response.headers.add_header('content-type', 'text/plain')
        out = self.response.out
        impcmd = 'param'
        if ictx is None:
            if export:
                out.write("# Ghilbert interface file for context %s\n\n"
                          % vctx.name)
                # Don't write params, we want a unified export that is
                # all-in-one
                #
                # Write all kinds
                # Write all varibles
                # Write all terms
                # Write all stmts
                #  But problem: some of the terms & stmts, coming from imports
                #  of the vctx, may use variable definitions that are not
                #  native to the vctx, and could in principle be
                #  inconsistent with the variable definitions of the vctx.
                #  We don't have this problem if we don't do a unified
                #  export, and only export the terms and theorems
                #  introduced by the vctx itself...
                # Other question: How do we reconcile generated proven but
                # incomplete prop.ghi with complete unproven prop.ghi?
                #
                # For now, don't try a unified export.
            else:
                out.write("# Ghilbert proof file for context %s\n\n" % vctx.name)
                impcmd = 'import'
        else:
            fname = ctx.fname[len(gh_base_dir):]
            out.write("# Ghilbert interface file %s\n\n" % fname)

        # have to put out imports in order.
        for imp in ctx.iflist:
            # imp is (ifname, ictx, params, prefix,
            #         kindmap, termmap, cmdword)  for a verify context.
            # termmap and cmdword are missing for an interface context
            # skip exports
            if len(imp) == 7 and imp[6] == 'export':
                continue
            ifname, pctx, params, prefix, kindmap = imp[:5]
            #logging.info('imp=%r' % (imp,))
            if not pctx.fname.startswith(gh_base_dir):
                logging.error('Real interface path %s does not start with %s' %
                              (pctx.fname, gh_base_dir))
                raise verify.VerifyError('Bad path prefix')
            fname = pctx.fname[len(gh_base_dir):]
            if pctx.name is not None:
                fname = fname + 'i'
            out.write('%s (%s %s (%s) "%s")\n' %
                      (impcmd, ifname, fname,
                       ' '.join([ctx.iflist[p][0] for p in params]), prefix))

        out.write('\n')

        # note, all kinds in verify context or export come from
        # import/param
        if ictx is not None:
            for k in ictx.kind_hist:
                if k[1] >= 0:
                    continue  # skip kinds originating in other interfaces
                out.write('kind (%s)\n' % k[0])

        # kindbinds
        for k in ctx.kindbinds:
            kix = ctx.kinds[k]
            kv = ctx.kind_hist[kix]
            out.write('kindbind (%s %s)\n' % (kv[0], k))
        out.write('\n')

        varkinds = {}
        for vv in ctx.syms.itervalues(): # hmm, too many stmt/thm/defthm
            if vv[0] == 'var' or vv[0] == 'tvar':
                if len(vv) == 4:
                    kname = vv[3]
                else:
                    kname = ctx.kind_hist[vv[1]][0]
                try:
                    prl = varkinds[kname]
                except KeyError:
                    prl = ([],[])
                    varkinds[kname] = prl
                if vv[0] == 'tvar':
                    prl[0].append(vv[2])
                else:
                    prl[1].append(vv[2])
        for kname, prl in varkinds.iteritems():
            if prl[0] != []:
                prl[0].sort()    
                out.write('tvar (%s %s)\n' % (kname, ' '.join(prl[0])))
            if prl[1] != []:
                prl[1].sort()    
                out.write('var (%s %s)\n' % (kname, ' '.join(prl[1])))
        out.write('\n')

        if ictx is None:
            for thname in vctx.assertion_hist:
                thm = vctx.syms[thname]
                record = thm[7]
                if isinstance(record, tuple):
                    cmd, termname = record
                else:
                    cmd, termname = record, None
                if export:
                    if termname is not None:
                        tm = vctx.term_hist[vctx.terms[termname]]
                        # tm is (termname, ifindex, termix_orig,
                        #        rkind, argkinds, freemap, sig)
                        out.write('term %s\n' %
                                  vctx.term_arg_string(tm[3], tm[6], tm[5]))
                    varlist = thm[4]
                    fv = []
                    for clause in thm[1]:
                        fv.append(vctx.iexps_to_string(clause, varlist))
                    out.write("stmt (%s (%s) %s %s)\n" %
                              (thname,
                               ' '.join(fv),
                               vctx.iexps_to_string(thm[2], varlist),
                               vctx.iexp_to_string(thm[3], varlist)))
                else:
                    out.write('%s\n\n' % cmd) # preserves comments

            for nm, ul in vctx.unresolved_thms.iteritems():
                if isinstance(nm, tuple):
                    nm = "term '%s'" % nm[0]
                else:
                    nm = "assertion '%s'" % nm
                out.write("\n## Depend on unresolved %s\n" % nm)
                for u in ul:
                    out.write("#%s %s\n" % (u[-3],
                                            verify.sexp_to_string(u[-2])))
            
            return    # done for verify context.

        for tm in ictx.term_hist:
            if tm[1] >= 0:
                continue
            # tm is (termname, ifindex, termix_orig,
            #        rkind, argkinds, freemap, sig)
            out.write('term %s\n' %
                      ictx.term_arg_string(tm[3], tm[6], tm[5]))

        out.write('\n')
        # order the axioms better?
        for label in ictx.assertion_hist:
            stmt = ictx.syms[label]
            out.write("%s\n\n" % stmt[7])
        return


class EditPage(webapp.RequestHandler):
    def get(self, name):
        global gh_global_ctx
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
        full_pname = os.path.join(gh_base_dir, name[1:])
        try:
            gh_ctx = gh_global_ctx.all_interfaces[full_pname]
            ps = (full_pname, '')
        except KeyError:
            ps = os.path.split(full_pname)
            try:
                gh_ctx = gh_global_ctx.all_interfaces[ps[0]]
            except KeyError:
                self.error(404)
                return
        if gh_ctx.name is None: # only allow verify contexts, for now
            self.error(404)
            return
        ps = (ps[0][len(gh_base_dir):], ps[1])
        hist = gh_ctx.assertion_hist
        thmname = ps[1]
        existing_thm = ''
        if thmname == '':
            thmname = 'New theorem'
            cmd = None
        else:
            if thmname == 'LAST': # Get latest theorem
                n = len(hist)
                if n == 0:
                    self.error(404)
                    return
                thmname = hist[n - 1]
            thm = gh_ctx.syms.get(thmname, None)
            if thm is None:
                cmd = "# No theorem named '%s' was found." % thmname
            elif thm[0] not in ('thm', 'defthm'):
                cmd = "# '%s' is not a theorem." % thmname
            else:
                cmd = thm[7]
                if isinstance(cmd, tuple): #defthm has (cmd, deftermname)
                    cmd = cmd[0]
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
  <label for="exist_thm">Edit existing theorem named: </label><input type="text" id="exist_thm" value="%s"/><br/>
  <textarea id="canvas" cols="80" rows="20" width="640" height="480" tabindex="0"></textarea><br/>
  <input type="button" id="save" onclick="GH.save(document.getElementById('canvas').value)" name="save" value="save"/><br/>
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
uc = new GH.XhrUrlCtx('/ctx', url);
v = new GH.VerifyCtx(uc, run);
v.drop_thm(document.getElementById('exist_thm').value)
run(uc, url, v);
var mainpanel = new GH.TextareaEdit(document.getElementById('canvas'));
window.direct = new GH.Direct(mainpanel, document.getElementById('stack'));
window.direct.vg = v;
var exist_thm = document.getElementById('exist_thm');
exist_thm.onchange = function() {
    var thmname = exist_thm.value;
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
        self.response.out.write(simplejson.dumps([1, 2]) + "\n")
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
        self.response.headers.add_header('content-type', 'text/plain')
        for line in lines:
            self.response.out.write(line)

class MainPage(webapp.RequestHandler):
    def get(self):
        global gh_global_ctx
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
        if gh_global_ctx is None:
            out.write('</body>\n')
            return
        for ctx in gh_global_ctx.interface_list:
            fn = ctx.fname
            pfn = fn[len(gh_base_dir):]
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
        self.response.headers.add_header('content-type', 'text/plain')
        res = GHDatastoreUpdate(100)
        out.write('%s\r\n' % res)

class ResetPage(webapp.RequestHandler):
    def get(self):
        out = self.response.out
        if not users.is_current_user_admin():
            self.error(401)
            self.response.headers.add_header('content-type', 'text/plain')
            out.write('401 Unauthorized.')
            return
        gh_edit_gen_refresh()
        out.write("""<title>Reset to Factory Defaults</title>
        
<body style="background-color:black;color:yellow">
<h1>Reset Ghilbert to Factory Defaults</h1>
<h2><em>Warning</em>: Pressing the big red button will destroy all work not present in the factory default files!</h2>
<p>
<a href="/">Go Home</a>
<br>
<br> <label for="step_num" id="step_label"> </label>
<br> <input type="button" id="reset" style="background-color:red;color:black;width:100px;height:50px" onclick="factory_reset()" name="reset" value="Reset"/>
<script type="text/javascript">
factory_reset = function () {
    var req = new XMLHttpRequest();
    req.open('POST', '/reset', true);
    var oldresp = null
    var label = document.getElementById('step_label');
    var rsc_func = function () {
        if (req.readyState != 4) {
            return;
        }
        if (req.status != 200) {
            label.innerHTML += ' ERROR: ' + req.status;
            req.abort()
            req = null
            return
        }
        resp = req.responseText;
        if (resp.substring(0, 4) === 'done') {
            req = null
            window.location.href = '/'
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
        req.send('');
    };
    req.onreadystatechange = rsc_func;
    req.setRequestHeader('Content-Type', 'application/x-www-form-urlencoded');
    label.innerHTML = '';
    req.send('');
};

</script>
""")
        return

    def post(self):
        global gh_edit_gen
        global gh_dsinit
        out = self.response.out
        self.response.headers.add_header('content-type', 'text/plain')
        if not users.is_current_user_admin():
            self.error(401)
            out.write('401 Unauthorized.')
            return
        if gh_edit_gen[1] is None and gh_edit_gen_refresh() == 0:
            egen = EditGeneration(gen=0)
            egen.put()
            gh_edit_gen = (0, egen)
        if gh_dsinit is None:
            defaults = [
                ('PROP', '/peano/prop.gh'),
                ('PRED', '/peano/pred.gh'),
                ('PEANO', '/peano/peano_thms.gh'),
                ('PEANO_SET', '/peano/peano_set.gh'),
                ]
            gh_dsinit = GHDatastoreReset(gh_edit_gen[1].key(), defaults, 40)
        try:
            val = gh_dsinit.next()
        except StopIteration:
            gh_dsinit = None
            egen = gh_edit_gen[1]
            egen.gen = gh_edit_gen[0] + 0x100000000
            egen.put()
            out.write('done')
            return
        out.write('%s' % val)
        return

class EditGenPage(webapp.RequestHandler):
    def get(self):
        global gh_edit_gen
        self.response.headers.add_header('content-type', 'text/plain')
        out = self.response.out
        edit_gen = gh_edit_gen_refresh()
        out.write('0x%x\n' % edit_gen)

application = webapp.WSGIApplication(
                                     [('/', MainPage),
                                      ('/recent', RecentPage),
                                      ('/peano/(.*)', StaticPage),
                                      ('/edit(.*)', EditPage),
                                      ('/env(/.*)?', PrintEnvironmentHandler),
                                      ('/ctx(.*)', ContextHandler),
                                      ('/save', SaveHandler),
                                      ('/reset', ResetPage),
                                      ('/update', UpdateHandler),
                                      ('/egen', EditGenPage),
                                      ], debug=True)

gh_base_dir = os.path.realpath(os.getcwd())  # realpath not necessary?

def main():
    run_wsgi_app(application)

if __name__ == "__main__":
    main()
