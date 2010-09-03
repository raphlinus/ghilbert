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

# Reference implementation for Ghilbert - still in draft

import sys
import os.path
import array


# for debug printing
def sexp_to_string(sexp):
    buf = array.array('c')
    sexp_to_string_rec(buf, sexp)
    return buf.tostring()
def sexp_to_string_rec(buf, sexp):
    if type(sexp) == type('str'):
        buf.fromstring(sexp)
    elif type(sexp) == type([]):
        buf.fromstring('(')
        sp_string = ''
        for el in sexp:
            buf.fromstring(sp_string)
            sexp_to_string_rec(buf, el)
            sp_string = ' '
        buf.fromstring(')')

def iexp_to_string_rec(buf, iexp, varlist, term_hist):
    if isinstance(iexp, list):
        buf.fromstring('(')
        buf.fromstring(term_hist[iexp[0]][0])
        for el in iexp[1:]:
            buf.fromstring(' ')
            iexp_to_string_rec(buf, el, varlist, term_hist)
        buf.fromstring(')')
        return
    buf.fromstring(varlist[iexp][2])

class ErrorMark(object):
    ## Stored in the GhilbertCtx cmd_hist 'undo' slot to mark an error.
    def __init__(self, msg, undo_info):
        self.msg = msg
        self.undo_info = undo_info

class VerifyError(Exception):
    def __init__(self, why, label = None, proofctx = None):
        self.why = why
        self.label = label
        self.proofctx = proofctx
        self.step = None

class ScannerRec:
    def __init__(self, instream, record=None):
        self.instream = instream
        self.line = ''
        self.pos = 0
        self.lineno = 0
        self.record = record

    def get_tok(self):
        record = self.record
        jx = self.pos
        line = self.line
        while True:
            # Skip initial spaces. ASCII 0x20 is the only non-line-ending
            # whitespace that we allow.
            while jx != len(line) and line[jx] in ' \n':
                jx += 1
            if jx == len(line) or line[jx] == '#':
                if record is not None:
                    record += line[self.pos:]
                self.pos = 0
                self.line = ''
                line = self.instream.readline()
                self.lineno += 1
                if line == '':
                    self.record = record
                    return None
                jx = 0
                continue
            break
        ix = jx
        self.line = line
        # Note, we disallow '\t' and other control characters except for
        # '\n' or '\r'
        # The first character is not in '# \n\r' by the above loop and
        # the universal newline conversion done by readline().
        while jx != len(line) and line[jx] not in '() \n#':
            n = ord(line[jx])
            if n < 32 or n >= 127:
                raise SyntaxError('Illegal byte (ord=%d) in file\n' % n)
            jx = jx + 1
        if jx == ix:
            # Must be '(' or ')'
            jx += 1
        if record is not None:
            record += line[self.pos:jx]
        self.pos = jx
        self.record = record
        return line[ix:jx]

    def end_record(self):  # only called if self.record is not None.
        record = self.record
        self.record = ''
        return record

##class Scanner:
##    def __init__(self, instream):
##        self.instream = instream
##        self.lineno = 0
##        self.toks = []
##        self.tokix = 0
##    def get_tok(self):
##        while len(self.toks) == self.tokix:
##            line = self.instream.readline()
##            self.lineno += 1
##            if line == '':
##                return None
##            line = line.split('#')[0]
##            line = line.replace('(', ' ( ')
##            line = line.replace(')', ' ) ')
##            self.toks = line.split()
##            self.tokix = 0
##        result = self.toks[self.tokix]
##        self.tokix += 1
##        return result

def read_sexp(scanner):
    while 1:
        tok = scanner.get_tok()
        if tok == None:
            return None
        if tok == '(':
            result = []
            while 1:
                subsexp = read_sexp(scanner)
                if subsexp == ')':
                    break
                elif subsexp == None:
                    raise SyntaxError('eof inside sexp')
                result.append(subsexp)
            return result
        else:
            return tok

class UrlCtx:
    def __init__(self, repobase, basefn, instream):
        self.repobase = repobase              # base for absolute paths
        if basefn[0] == '/':
            basefn = os.path.join(repobase, basefn[1:])
        self.base = os.path.split(basefn)[0]  # base for relative paths
        self.instream = instream

    def normalize(self, url, caller_fname):
        #self.out.write('UrlCtx.normalize(%s)\n' % url)
        #self.out.write('  base=%s, repobase=%s\n' % (self.base, self.repobase))
        if url == '-':
            return url
        if url.startswith('file://'):
            fn = url[7:]
        elif url.startswith('/'):
            fn = os.path.join(self.repobase, url[1:])
        else:
            caller_dir = os.path.split(caller_fname)[0]
            fn = os.path.join(caller_dir, url)
        fn = os.path.realpath(fn)
        #self.out.write('  fn=%s\n' % fn)
        return fn

    def resolve(self, url, caller_fname):
        """ Return a stream corresponding to url within this context. """
        # need to be careful about security if used on malicious inputs
        fn = self.normalize(url, caller_fname)
        if fn == '-':
            return self.instream
        try:
            f = open(fn, 'r')
        except IOError:
            raise VerifyError("Cannot open '%s' (url '%s')" % (fn, url))
        return ScannerRec(f)

class ProofCtx:
    def __init__(self, label, ifv, ihyps, iconcl,
                 varlist, varmap, num_hypvars, num_nondummies, fvvarmap):
        self.label = label
        self.ifv = ifv
        self.ihyps = ihyps
        self.iconcl = iconcl
        self.varlist = varlist
        self.varmap = varmap
        self.num_hypvars = num_hypvars
        self.num_nondummies = num_nondummies
        self.stack = []
        self.mandstack = []
        self.fvvarmap = fvvarmap
        self.defterm = None

# The purpose of the GlobalCtx object is to
# - map urls to GhilbertCtx objects;
# - hold any additional data that is shared by the interdependent
#   Ghilbert contexts in the system.
# The primary method provided by this class is fetch_interface(),
# which fetches the GhilbertCtx object corresponding to a url
# on behalf of a calling context.
class GlobalCtx(object):
    def __init__(self, urlctx, cookie=None):
        self.all_interfaces = {} # maps urls to GhilbertCtx's
        self.interface_list = []
        self.iface_in_progress = {}
        self.urlctx = urlctx
        self.cookie = cookie

    def start_context(self, ctx):
        self.iface_in_progress[ctx.fname] = ctx

    def complete_context(self, ctx):
        del self.iface_in_progress[ctx.fname]
        self.all_interfaces[ctx.fname] = ctx
        self.interface_list.append(ctx)

    def fetch_interface(self, url, caller_ctx):
        """ Return the GhilbertCtx corresponding to url, on behalf of
            caller_ctx.
        """
        # TODO: normalize should take into account caller_ctx.fname
        fn = self.urlctx.normalize(url, caller_ctx.fname)
        if fn in self.iface_in_progress:
            raise VerifyError("Recursive fetch for interface file '%s'" % fn)

        pif = self.all_interfaces.get(fn, None)
        if pif != None:
            if pif.name is not None:
                raise VerifyError(
                    'Attempt to import/export/param a proof-file context %s.'
                    % fn)
            return pif

        # Note, build_interface is a variable attribute, not a member function,
        # of self.
        pif = self._build_interface(caller_ctx, fn, url)

        if pif.level >= caller_ctx.level:
            caller_ctx.level = pif.level + 1
        return pif

    def _build_interface(self, ctx, fn, url):
        """ An interface corresponding to normalized filename fn does not
            yet exist. Create and read this interface, for use by the
            calling context ctx, which imported/exported/param'ed it
            using the name url.  Returns a GhilbertCtx.
        """
        pif = InterfaceCtx(self, fn)
        pif.out = ctx.out
        pif.record = ctx.record
        scanner = self.urlctx.resolve(url, ctx.fname)
        scanner.record = ctx.record
        if not self.run(scanner, url, pif):
            raise VerifyError ("Failed while loading interface '%s'" % url)
        self.complete_context(pif)
        return pif

    def run(self, scanner, url, ctx):
        record = scanner.record
        try:
            while 1:
                cmd = read_sexp(scanner)
                if cmd is None:
                    return True
                if type(cmd) != str:
                    raise SyntaxError('cmd must be atom: %s has type %s' %
                                      (cmd, type(cmd)))
                arg = read_sexp(scanner)
                ctx.do_cmd(cmd, arg, (None if record is None
                                      else scanner.end_record()))
        except VerifyError, x:
            ctx.out.write('Verify error at %s:%d:\n%s\n' %
                          (url, scanner.lineno, x.why))
        except SyntaxError, x:
            ctx.out.write('Syntax error at line %s:%d:\n%s\n' %
                          (url, scanner.lineno, str(x)))
        ctx.count_error()
        return False


# Map terms in an internal expression.
def map_syms(iexp, termmap):
    if not isinstance(iexp, list):
        return iexp
    return [termmap[iexp[0]]] + [map_syms(x, termmap) for x in iexp[1:]]

def apply_subst(templ, env):
    if not isinstance(templ, list):
        return env[templ]
    return [templ[0]] + [apply_subst(el, env) for el in templ[1:]]


class UnifyError(Exception):
    def __init__(self, e1, e2):
        self.e1 = e1
        self.e2 = e2

# match templ, which is an internalized expression in the variable space
# of the assertion being applied, against exp, an internalized expression
# in the variable space of the current proof, updating list env, considered
# as a mapping from the variable indices in the template space to
# internalized expressions in the current proof
def match(templ, exp, env):
    if not isinstance(templ, list):
        if env[templ] >= 0:
            if exp != env[templ]:
                # todo: more debug detail
                raise UnifyError(templ, exp)
        else:
            # Note, we check elsewhere if a binding variable is matched
            # against a non-binding-variable term.
            env[templ] = exp
        return

    if not isinstance(exp, list):
        raise UnifyError(templ, exp)
    if templ[0] != exp[0]:
        raise UnifyError(templ, exp)
    for i in range(1, len(templ)):
        match(templ[i], exp[i], env)

class GhilbertCtx(object):
    def __init__(self, global_ctx, fname):
        self.kinds = {}         # kind names to indices in kind_hist
        self.kind_hist = []     # (prefixed_kind, ifindex, orig_kind)
        self.kindbinds = []     # kind aliases introduced by this context
        self.terms = {}
        self.term_hist = []
        self.syms = {}
        self.interfaces = {}  # maps interface names to indices in iflist
        self.iflist = []  #list of (ifname, ictx, params, prefix,
                          #         kindmap, termmap, style)
                          # where style is 'import' or 'export'
        self.global_ctx = global_ctx
        self.error_count = 0
        self.fname = fname  # Absolute, normalized 'URL' for this context.
        self.level = 0
        self.name = None
        self.verbosity = 1
        self.out = sys.stdout
        self.record = None
        global_ctx.start_context(self)
        # Each Ghilbert command processed adds 4 entries to self.cmd_hist
        # The information saved is chosen to make it easy to reproduce
        # the text of the commands, and to be able to undo commands in reverse
        # order.  Only commands that consist of a valid atom followed by a
        # valid s-expression list are saved. Commands that are not successful
        # will nevertheless be saved in the history, but processing such
        # unsuccessful commands must have _no_ effect on the context state.
        # A command that is partially successful (e.g. a var command that
        # succeeds in adding only some of its listed variables, or an
        # import command that encounters an error partway through) must
        # generate undo information for the part of the command that succeeds,
        # and the part of the command that does not succeeds mut have no
        # effect and generate no additional undo information.
        # [0] The command word.
        # [1] The command argument s-expression.
        # [2] The text of the command, including any preceding comments and
        #     whitespace.
        # [3] A reference to information useful in undoing the command's
        #     effect, or None if the command was unsuccessful and had no
        #     effect. Used by the undo_cmd() method.
        self.cmd_hist = None
        self.badthms = {}

    def record_error(self, errstr):
        self.error_count = self.error_count + 1
        self.out.write("%s\n" % errstr)
        cmd_hist = self.cmd_hist
        assert(cmd_hist is not None)

        cnum = len(self.cmd_hist) - 4
        assert(cnum >= 0)
        cmd = cmd_hist[cnum]
        undo = cmd_hist[cnum + 3]
        cmd_hist[cnum + 3] = ErrorMark(errstr, undo)
        if cmd in ('thm', 'defthm'):
            arg = cmd_hist[cnum + 1]
            if (isinstance(arg, list) and len(arg) > 0 and
                isinstance(arg[0], basestring)):
                label = arg[0]
                l = self.badthms.get(label)
                if l is None:
                    l = []
                    self.badthms[label] = l
                else:
                    self.out.write(
                        'Warning: repeated bad assertion named %s\n')
                l.append(cnum)

    def undo_to(self, cmd_ix):
        cmd_hist = self.cmd_hist
        assert(cmd_hist is not None)
        maxcmd = len(cmd_hist) / 4
        assert(0 <= cmd_ix <= maxcmd)
        while maxcmd > cmd_ix:
            self.undo_cmd()
            maxcmd -= 1

    def apply_hist(self, hist):
        maxhist = len(hist)
        assert((maxhist & 3) == 0)
        ix = 0
        while ix < maxhist:
            try:
                self.do_cmd(hist[ix], hist[ix + 1], hist[ix + 2])
            except VerifyError, x:
                self.record_error('Verify error: %s' % x.why)
            except SyntaxError, x:
                self.record_error('Syntax error: %s' % str(x))
            ix += 4

    def count_error(self):
        self.error_count = self.error_count + 1

    def get_kind(self, kname):
        try:
            return self.kinds[kname]
        except KeyError:
            raise VerifyError("Unknown kind '%s'" % kname)
        except TypeError:
            raise VerifyError("Expected kind name, found: %s" %
                              sexp_to_string(kname))

    def add_kind(self, kind, val):
        if kind in self.kinds:
            raise VerifyError("Kind '%s' already defined" % kind)
        self.kinds[kind] = val

    def kindbind_cmd(self, arg):
        if not isinstance(arg, list) or len(arg) != 2 or \
               not isinstance(arg[1], basestring):
            raise SyntaxError("Expected 'kindbind (OLDKIND NEWKIND)'")
        self.add_kind(arg[1], self.get_kind(arg[0]))
        self.kindbinds.append(arg[1])
        return

    def add_sym(self, label, val):
        if label in self.syms:
            raise VerifyError('Symbol ' + label + ' already defined')
        self.syms[label] = val

    def add_assertion(self, kw, label, fv, hyps, concl, varlist,
                      num_hypvars, num_nondummies):
        self.add_sym(label, (kw, fv, hyps, concl,
                             varlist, num_hypvars, num_nondummies))

    # Check well-formedness of the expression exp and return its kind.
    # Add the variables found to varlist and varmap: the former is a list
    # of items syms[v] for each variable v found, and varmap maps the names
    # of found variables to their indices in varlist.
    # Return a tuple (kw, kindix, iexpr) where kw is 'term', 'var', or 'tvar',
    # kindix is the kind (index) of the expression, and iexpr is the internal
    # form of the expression.
    # The internal form of a variable is just the variable's index in varlist.
    # The internal form of a term is a list, with the term symbol replaced
    # with the term index, and the term arguments converted to internal form.
    def internalize(self, exp, varlist, varmap):
        """ Check that exp is a well-formed expression, and return its kind """
        if isinstance(exp, basestring):
            try:
                ix = varmap[exp] # this may fail
                v = varlist[ix]  # this won't
            except KeyError:
                try:
                    v = self.syms[exp]
                except KeyError:
                    raise VerifyError('Not a known variable: ' + exp)
                # v is (kw, kindex, name, kname)
                if v[0] not in ('var', 'tvar'):
                    raise VerifyError('Symbol not a variable: ' + exp)
                ix = len(varlist)
                varmap[exp] = ix
                varlist.append(v)
            # ugh, packing & unpacking into tuples
            return (v[0], v[1], ix)

        # Else, exp is a list

        if len(exp) == 0:
            raise VerifyError("term can't be empty list")
        if not isinstance(exp[0], basestring):
            raise VerifyError('term must be id, found ' +
                              sexp_to_string(exp[0]))
        try:
            termix = self.terms[exp[0]]
        except KeyError:
            raise VerifyError("term '%s' not known" % exp[0])

        term = self.term_hist[termix]
        # term is (termname, ifindex, termix_orig,
        #          rkind, argkinds, freemap, sig [, defthm_label])
        nargs = len(term[4])
        if len(exp) - 1 != nargs:
            print exp, term
            raise VerifyError(
                'Arity mismatch: %s has arity %d but was given %d arguments' %
                (exp[0], nargs, len(exp) - 1))
        result = [termix]
        for i in range(nargs):
            child = self.internalize(exp[i + 1], varlist, varmap)
            if term[5][i] >= 0 and child[0] != 'var':
                raise VerifyError('Expected a binding variable, but found: '
                                  + sexp_to_string(exp))
            if child[1] != term[4][i]:
                raise VerifyError(
                    'Kind mismatch: in %s, argument %d does not have kind %s' %
                    (sexp_to_string(exp), i, self.kind_hist[term[4][i]][0]))
            result.append(child[2])
        # ugh, packing & unpacking into tuples
        return ('term', term[3], result)

    def iexp_to_string(self, iexp, varlist):
        buf = array.array('c')
        iexp_to_string_rec(buf, iexp, varlist, self.term_hist)
        return buf.tostring()

    def iexps_to_string(self, iexps, varlist):
        buf = array.array('c')
        space = ''
        buf.fromstring('(')
        for iexp in iexps:
            buf.fromstring(space)
            iexp_to_string_rec(buf, iexp, varlist, self.term_hist)
            space = ' '
        buf.fromstring(')')
        return buf.tostring()

    def iface_kinds(self, ictx, params, prefix, export=False):
        if self.cmd_hist is None:
            kind_undo_list = None
            kindbind_undo_list = None
        else:
            kind_undo_list = self.cmd_hist[-1][1]
            kindbind_undo_list = self.cmd_hist[-1][2]
        ifindex = len(self.iflist)
        nk = len(ictx.kind_hist)
        kindmap = [-1]*nk
        for ix in xrange(nk):
            k = ictx.kind_hist[ix]
            # k is (kindname_in_ictx, ifindex_in_ictx, kindix_orig)
            kifindex = k[1]
            if kifindex >= 0:
                kmap = self.iflist[params[kifindex]][4]
                kindmap[ix] = kmap[k[2]]
                continue   # Don't add kinds not provided by ictx itself
            kpref = prefix + k[0]
            if export:
                try:
                    kix = self.kinds[kpref]
                except KeyError:
                    raise VerifyError("No kind '%s' exists in verify context."
                                      % kpref)
                kindmap[ix] = kix
            else:
                if kpref in self.kinds:
                    raise VerifyError("A kind '%s' already exists." % kpref)
                n = len(self.kind_hist)
                self.kinds[kpref] = n
                self.kind_hist.append((kpref, ifindex, ix))
                if kind_undo_list is not None:
                    kind_undo_list.append(kpref)
                kindmap[ix] = n

        # Imported kindbinds
        for kname in ictx.kindbinds:
            kix = ictx.kinds[kname]
            k = ictx.kind_hist[kix]
            kpref = prefix + kname
            ix = kindmap[kix]
            if export:
                try:
                    ekix = self.kinds[kpref]
                except KeyError:
                    raise VerifyError("No kind '%s' exists in verify context."
                                      % kpref)
                if ekix != ix:
                    raise VerifyError("Inconsistent kindbind for %s in export"
                                      % kpref)
            else:
                if kpref in self.kinds:
                    raise VerifyError("A kind '%s' already exists." % kpref)
                self.kinds[kpref] = ix
                if kindbind_undo_list is not None:
                    kindbind_undo_list.append(kpref)

        return kindmap

    def iface_terms(self, ictx, params, prefix, kindmap, export=False):
        if self.cmd_hist is None:
            term_undo_list = None
        else:
            term_undo_list = self.cmd_hist[-1][3]
        ifindex = len(self.iflist)
        nt = len(ictx.term_hist)
        #self.out.write('ictx %s knows %d terms\n' % (ictx.fname, nt))
        termmap = [-1]*nt
        for ix in xrange(nt):
            t = ictx.term_hist[ix]
            #self.out.write('  %s\n' % t[0])
            # t is (termname_in_ictx, ifindex_in_ictx, termix_orig,
            #       rkind, argkinds, freemap, sig [, defterm_label])
            # Note that rkind and the elements of argkinds are kind indices
            # in ictx.kind_hist, and need to be translated.
            # signature is the term signature in the originating interface
            tifindex = t[1]
            if tifindex >= 0:
                tmap = self.iflist[params[tifindex]][5]
                termmap[ix] = tmap[t[2]]
                continue   # skip kinds not provided by ictx itself
            vrkind = kindmap[t[3]]
            vargkinds = [kindmap[ak] for ak in t[4]]
            tpref = prefix + t[0]
            if export:
                try:
                    vix = self.terms[tpref]
                except KeyError:
                    raise VerifyError("No term '%s' exists in verify context."
                                      % tpref)
                vtv = self.term_hist[vix]
                if vtv[3] != vrkind or vtv[4] != vargkinds or vtv[5] != t[5]:
                    raise VerifyError(
                        "Exported term '%s' does not match '%s' in verify context" %
                        (t[0], tpref))
                termmap[ix] = vix
            else:
                if tpref in self.terms:
                    raise VerifyError("A term '%s' already exists." % tpref)
                tv = (tpref, ifindex, ix, vrkind, vargkinds, t[5], t[6])
                n = len(self.term_hist)
                self.terms[tpref] = n
                self.term_hist.append(tv)
                if term_undo_list is not None:
                    term_undo_list.append(tpref)
                termmap[ix] = n

        return termmap

    def term_arg_string(self, rkind, sig, freemap):
        rkname = self.kind_hist[rkind][0]
        buf = array.array('c')
        buf.fromstring("(")
        buf.fromstring(rkname)
        buf.fromstring(" (")
        space = ''
        for s in sig:
            buf.fromstring(space)
            buf.fromstring(s)
            space = ' '
        buf.fromstring(')')
        for ix in xrange(len(freemap)):
            bmap = freemap[ix]
            if bmap <= 0:
                continue    # skip non-binding and fully-bound arguments
            bvar = sig[1 + ix]
            buf.fromstring(" (")
            buf.fromstring(bvar)
            jx = 0
            po2 = 1
            while po2 <= bmap:
                if (po2 & bmap) != 0:
                    buf.fromstring(" ")
                    buf.fromstring(sig[1 + jx])
                jx += 1
                po2 <<= 1
            buf.fromstring(")")
        buf.fromstring(")")
        return buf.tostring()


class VerifyCtx(GhilbertCtx):
    def __init__(self, global_ctx, fname, fail_continue=False):
        GhilbertCtx.__init__(self, global_ctx, fname)
        self.fail_continue = fail_continue
        self.ignore_exports = False

    def add_term(self, label, t):
        if label in self.terms:
            raise VerifyError("Term '%s' already defined" % label)
        self.terms[label] = t # (kind, argkinds, freemap, sig, ctx)
    def allvars(self, iexp):
        fv = []
        self.allvars_rec(iexp, fv)
        return fv
    def allvars_rec(self, iexp, fv):
        if isinstance(iexp, list):
            for subexp in iexp[1:]:
                self.allvars_rec(subexp, fv)
            return
        if not iexp in fv:
            fv.append(iexp)
        return

    def free_scan(self, var, term, accum):
        if not isinstance(term, list):
            return accum(term)

        t = self.term_hist[term[0]]
        # t is (termname, ifindex, termix_orig,
        #       rkind, argkinds, freemap, sig [, defterm_label])
        freemap = t[5]
        # In the following loop, v is the 0-based term argument
        # index for each binding variable argument of the term, while
        # m is the corresponding bitmap of 0-based term argument indices
        # in which that binding variable argument might occur free.
        # If var is used as a binding variable argument of term, restrict
        # the subterms in which var might occur free accordingly.
        nargs = len(freemap)
        subterms = (1 << nargs) - 1  # bitmap of all argument positions
        for v in xrange(nargs):
            m = freemap[v]
            if m < 0:
                continue  # skip non-binding variables
            if term[v + 1] == var:
                subterms = subterms & m
        po2 = 1
        v = 1
        while po2 <= subterms:
            if (po2 & subterms) != 0:
                if self.free_scan(var, term[v], accum):
                    return True
            v = v + 1
            po2 = (po2 << 1)
        return False


    def free_in(self, var, term, fvvars, varlist):
        return self.free_scan(var, term,
            lambda v :
               (True if v == var or
                        (fvvars != None and
                         varlist[v][0] == 'tvar' and
                         v not in fvvars)
                     else False))

    # Check if binding variable var occurs free in term.
    # This routine returns True if and only if var occurs _explicitly_ free
    # in fvvars.
    # If fvvars is not None, it is a dictionary. In that case, the domain of
    # fvvars consists of some term variable (indices) in the theorem being
    # proved.
    #  - If fvvars[A] >= 0, the constraint context for the theorem being proven
    #    guarantees that binding variable var does not occur free in A.
    #  - If fvvars[A] == 0, the constraint mentioned above has not been
    #    required by the proof yet.
    #  - If fvvars[A] > 0, the constraint mentioned above has been required
    #    by the proof.
    #  - If fvvars[A] is None, the proof has required that var not occur free
    #    in A, but no such constraint was provied by the theorem's constraint
    #    context.
    #  - If A is not in fvvars, then the theorem's constraint context does not
    #    contain the pair (A var), but that pair has not yet been required by
    #    the proof either.
    # This routine updates fvvars to maintain the above conditions.
    # If fvvars is None, check for explicit freeness of var in term.
    def check_free_in(self, var, term, fvvars, varlist):
        def checker(v, var=var, fvvars=fvvars, varlist=varlist):
            if v == var:
                return True  # only stop scan if var explicitly free.
            if fvvars == None or varlist[v][0] == 'var':
                return False
            try:
                val = fvvars[v]
            except KeyError:
                fvvars[v] = None
                return False
            if val == 0:
                fvvars[v] = 1
            return False
        return self.free_scan(var, term, checker)

    def freelist(self, bvar, exp, l, varlist):
        """ Append to l the list of variables occurring in exp for which
            binding variable bvar might occur free in exp if it occurs
            free in one of the variables of the list.
        """
        def checker(v, bvar=bvar, l=l, varlist=varlist):
            if v != bvar and varlist[v][0] == 'var':
                return False # different binding variables are distinct
            if v not in l:
                l.append(v)
            return False
        return self.free_scan(bvar, exp, checker)

    def check_params(self, ictx, ifname, paramnames):
        # Check that the parameter interfaces are all distinct(?) and all
        # correspond to existing interfaces.
        # Returns a list mapping indices of parameters passed to ictx,
        # to indices of the corresponding interfaces in self.iflist
        used = {}
        params = []
        try:
            for pn in paramnames:
                if pn in used:
                    raise VerifyError(
                      "Interface %s passed more than once to import context." %
                        pn)
                used[pn] = 0
                params.append(self.interfaces[pn])
        except KeyError:
            raise VerifyError("Unknown interface %s" % pn)
        except TypeError:
            raise SyntaxError("Non-atom provided as interface parameter.")

        n = len(params)
        if n != len(ictx.iflist):
            self.out.write('len(ictx.iflist)=%d\n' % len(ictx.iflist))
            for ifc in ictx.iflist:
                self.out.write("... %r\n" % (ifc,))
            raise VerifyError("Wrong number of parameters for interface '%s'" %
                              ifname)
        for ix in xrange(n):
            ifaceloc = self.iflist[params[ix]]
            ifaceimp = ictx.iflist[ix]
            # iflist entries are
            #   (ifname, ictx, params, prefix, kindmap, termmap, style)
            # Compare InterfaceCtx values for identity
            if ifaceimp[1] is not ifaceloc[1]:
                raise VerifyError("Parameter mismatch for interface '%s'" %
                                  ifname)
            # Check that ifaceimp was parametrized in ictx the same way
            # that ifaceloc was parametrized in self.
            impparams = ifaceimp[2]
            locparams = ifaceloc[2]
            for jx in xrange(len(impparams)):
                if locparams[jx] != params[impparams[jx]]:
                    raise VerifyError(
                        "Parameter mismatch (%d, %d) for interface '%s'"
                        % (ix, jx, ifname))
        return params


    # import InterfaceCtx ictx with the specified name, parameters, and prefix
    # paramnames is a list of the interface names of the parameter interfaces
    # passed to ictx, all of which have been previously imported (or exported)
    def gh_import(self, ictx, ifname, paramnames, prefix):

        params = self.check_params(ictx, ifname, paramnames)

        kindmap = self.iface_kinds(ictx, params, prefix)

        termmap = self.iface_terms(ictx, params, prefix, kindmap)

        if self.cmd_hist is None:
            assertion_undo_list = None
        else:
            assertion_undo_list = self.cmd_hist[-1][4]
        if ictx.name is None:
            allowable = ('stmt',)
        else:
            allowable = ('thm', 'defthm')
        for label, val in ictx.syms.iteritems():
            if not val[0] in allowable:
                continue
            kw, fv, hyps, concl, varlist, num_hypvars, num_nondummies, cmd_ix = val
            labelpref = prefix + label
            if labelpref in self.syms:
                raise VerifyError(
                    "Importing stmt '%s', a symbol of that name already exists"
                    % labelpref)
            # Now, translate the hypotheses and conclusion(s) by mapping
            # the term indices. Also, map the kinds in varlist.
            vhyps = [map_syms(hyp, termmap) for hyp in hyps]
            vconcl = map_syms(concl, termmap)
            vvarlist = [(v[0], kindmap[v[1]], v[2]) for v in varlist]
            self.syms[labelpref] = ('stmt', fv, vhyps, vconcl,
                                    vvarlist, num_hypvars, num_nondummies,
                                    cmd_ix)
            if assertion_undo_list is not None:
                assertion_undo_list.append(labelpref)

        ifindex = len(self.iflist)
        self.interfaces[ifname] = ifindex
        self.iflist.append((ifname, ictx, params, prefix,
                            kindmap, termmap, 'import'))

    def gh_export(self, ictx, ifname, paramnames, prefix):

        params = self.check_params(ictx, ifname, paramnames)
        
        kindmap = self.iface_kinds(ictx, params, prefix, True)

        termmap = self.iface_terms(ictx, params, prefix, kindmap, True)

        for label, val in ictx.syms.iteritems():
            if val[0] != 'stmt':
                continue
            kw, fv, hyps, concl, varlist, num_hypvars, num_nondummies, cmd_ix = val
            labelpref = prefix + label
            try:
                vstmt = self.syms[labelpref]
            except KeyError:
                raise VerifyError(
                    "Exported stmt '%s' does not exist in verify context."
                    % labelpref)
            # Now, translate the hypotheses and conclusion(s) by mapping
            # the term indices. Also, map the kinds in varlist.
            vhyps = [map_syms(hyp, termmap) for hyp in hyps]
            vconcl = map_syms(concl, termmap)
            if vstmt[0] == 'var' or vstmt[0] == 'tvar':
                raise VerifyError("Symbol '%s' exported as stmt is a variable in verify context." % labelpref)
            if fv != vstmt[1]:
                raise VerifyError("Free variable constraint context mismatch for exported stmt '%s'" % labelpref)
            if vhyps != vstmt[2]:
                raise VerifyError("Mismatch in hypotheses for exported stmt '%s'" % labelpref)
            if vconcl != vstmt[3]:
                raise VerifyError("Mismatch in conclusion for exported stmt '%s'" % labelpref)
            # Note, num_nondummies must match vstmt[6] since the hypotheses
            # and conclusions match.
            for ix in xrange(num_nondummies):
                v = varlist[ix]
                vv = vstmt[4][ix]
                if v[0] != vv[0] or kindmap[v[1]] != vv[1]:
                    raise VerifyError("Mismatch in variable list for exported stmt '%s'" % labelpref)

        ifindex = len(self.iflist)
        self.interfaces[ifname] = ifindex
        self.iflist.append((ifname, ictx, params, prefix,
                            kindmap, termmap, 'export'))

    def defthm_cmd(self, arg):
        # defthm (LABEL KIND (DEFSYM VAR ...)
        #           ((TVAR BVAR ...) ...) ({HYPNAME HYP} ...) CONC
        #           STEP ...)
        if len(arg) < 7:
            raise VerifyError('Expected at least 7 arguments to defthm')
        (label, dkind, dsig, fv, hyps, conc) = arg[:6]
        if self.verbosity > 0:
            self.out.write('defthm %s\n' % label)
        proof = arg[6:]
        try:
            proofctx = self.check_proof(label, fv, hyps, conc, proof,
                                        dkind, dsig)
        except VerifyError, x:
            self.out.write('Error in defthm %s: %s\n' % (label, x.why))
            if x.proofctx != None:
                stack = x.proofctx.stack
                for i in xrange(len(stack)):
                    self.out.write('P%d: %s\n' %
                              (i, self.iexp_to_string(stack[i],
                                                      x.proofctx.varlist)))
            raise x

        # Check that:
        # - The conclusion matches the remnant expression on the proof
        #   stack exactly, except for any uses of the new term
        #   being defined.
        # - The conclusion contains at least one use of the new term being
        #   defined.
        # - Every such occurrence of the new term being defined in the
        #   conclusion is identical: the actual term arguments must be
        #   exactly the formal argument variables specified in the
        #   definition term signature. (In particular, more complicated
        #   actual arguments that are term expressions are forbidden here.)
        # - Every occurrence of the new term in the conclusion matches a
        #   subexpression (its expansion or definiens) in the remnant
        #   according to the following rules:
        #     - The matched subexpression must be a term expression, not
        #       just a variable. The subexpression's kind must agree with
        #       the result kind specified for the new term.
        #     - Every such matching subexpression is identical.
        #       (Specifically, even definition dummy variables must be
        #       identical in all the expansions.)
        #     - Any variable in the matched subexpression that is not one
        #       of the corresponding definition term's use's actual
        #       arguments is called a definition dummy variable.  Each
        #       definition dummy variable must also be a proof dummy
        #       variable, that is, it must not occur in the hypotheses or
        #       conclusion of the theorem.
        #     - All definition dummy variables in the definiens must be
        #       binding variables, and must not occur explicitly free in
        #       the definiens. [Investigate how necessary this is.]
        #     - Every actual argument variable of the term use must occur
        #       in the matched subexpression. [This could be omitted.]
        t = proofctx.defterm
        freemap = t[2]
        remnant = proofctx.stack[0]
        result = [None]

        termix = len(self.term_hist) - 1
        idsig = [termix] + [proofctx.varmap[vn] for vn in dsig[1:]]
        try:
            self.def_conc_match(proofctx.iconcl, remnant, idsig,
                                freemap, proofctx, result)
        except VerifyError, x:
            x.why = ('The defthm conclusion\n ' + sexp_to_string(conc) +
                     '\nfails to match remnant\n ' +
                     self.iexp_to_string(remnant, proofctx.varlist)
                     + '\n*** ' + x.why)
            raise
        if result[0] == None:
            raise VerifyError("The term '" + dsig[0] +
               "' being defined does not occur in the defthm conclusion.")

        cmd_ix = (None if self.cmd_hist is None else len(self.cmd_hist) - 4)
        self.add_sym(label,
                     ('defthm', proofctx.ifv, proofctx.ihyps,
                      proofctx.iconcl, proofctx.varlist,
                      proofctx.num_hypvars, proofctx.num_nondummies, cmd_ix))
        # The term was already added to self.term_history in term_common
        # in self.check_proof(). Add it back to self.terms, too.
        self.terms[dsig[0]] = termix

    def do_cmd(self, cmd, arg, record=None):
        """ Command processing for Verify (proof file) context """
        cmd_hist = self.cmd_hist
        if cmd_hist is not None:
            cmd_hist.append(cmd)
            cmd_hist.append(arg)
            cmd_hist.append(record)
            cmd_hist.append(None)
        out = self.out
        if cmd == 'thm':
            # thm (LABEL ((TVAR BVAR ...) ...) ({HYPNAME HYP} ...) CONC
            #        STEP ...)
            if len(arg) < 5:
                raise VerifyError('Expected at least 5 args to thm')
            (label, fv, hyps, conc) = arg[:4]
            if self.verbosity > 0:
                out.write('thm %s\n' % label)
            proof = arg[4:]
            try:
                proofctx = self.check_proof(label, fv, hyps, conc, proof)
                if proofctx.stack[0] != proofctx.iconcl:
                    raise VerifyError(('\nConclusion mismatch. Wanted %s' %
                                       sexp_to_string(conc)),
                                      label, proofctx)
            except VerifyError, x:
                msg = 'error in thm %s:\n' % label
                if self.fail_continue:
                    msg = msg + x.why
                out.write(msg)
                if x.proofctx != None:
                    stack = x.proofctx.stack
                    for i in xrange(len(stack)):
                        out.write('P%d: %s\n' %
                                  (i, self.iexp_to_string(stack[i],
                                                          x.proofctx.varlist)))
                if not self.fail_continue:
                    raise x
                self.count_error()

            cmd_ix = (None if cmd_hist is None else len(cmd_hist) - 4)
            self.add_sym(label,
                         ('thm', proofctx.ifv, proofctx.ihyps, proofctx.iconcl,
                          proofctx.varlist,
                          proofctx.num_hypvars, proofctx.num_nondummies,
                          cmd_ix))
            if cmd_hist is not None:
                cmd_hist[-1] = label
            return

        if cmd == 'defthm':
            # self.defthm_cmd() plays games with temporarily adding
            # the new term so that it can be used in the conclusion
            # of the defthm (but not anywhere else). Make sure to clean
            # this up if things go pear-shaped.
            termix_orig = len(self.term_hist)
            try:
                self.defthm_cmd(arg)
            except:
                if len(self.term_hist) > termix_orig:
                    del self.term_hist[termix_orig:]
                raise
            if cmd_hist is not None:
                cmd_hist[-1] = (arg[0], arg[2][0])
            return

        if cmd in ('var', 'tvar'):
            kind = self.get_kind(arg[0])
            if cmd_hist is not None:
                cmd_hist[-1] = []
            for v in arg[1:]:
                # Save arg[0] too so we preserve the kind name in spite of
                # kindbinds...
                self.add_sym(v, (cmd, kind, v, arg[0]))
                if cmd_hist is not None:
                    cmd_hist[-1].append(v)
            return
        if cmd == 'kindbind':
            self.kindbind_cmd(arg)
            if cmd_hist is not None:
                cmd_hist[-1] = arg[1]
            return
        if cmd in ('import', 'export'):
            # import (IFACE URL (PARAMS) PREFIX)
            if type(arg) != type([]) or len(arg) != 4:
                raise SyntaxError("Expected '" + cmd +
                                  " (IFACE URL (PARAM ...) PREFIX)'")
            if cmd == 'export' and self.ignore_exports:
                return
            ifname = arg[0]
            url = arg[1]
            paramnames = arg[2]
            prefix = arg[3]
            if type(ifname) != type('name') or type(url) != type ('url') or \
               type(paramnames) != type([]) or type(prefix) != type('prefix'):
                raise SyntaxError("Expected '" + cmd + " (IFACE URL (PARAM ...) PREFIX)'")
            if len(prefix) < 2 or prefix[0] != '"' or prefix[-1] != '"':
                raise SyntaxError('Namespace prefix must be enclosed in quotes')
            prefix = prefix[1:-1]

            if ifname in self.interfaces:
                raise VerifyError("An interface named %s already exists." % ifname)
            if self.verbosity > 0:
                if cmd == 'import':
                    out.write('Importing %s\n' % ifname)
                else:
                    out.write('Exporting %s\n' % ifname)

            ctx = self.global_ctx.fetch_interface(url, self)

            if cmd_hist is not None:
                # ifname, kinds, kindbinds, terms, assertions
                cmd_hist[-1] = [ifname, [], [], [], []]
            try:
                if cmd == 'import':
                    self.gh_import(ctx, ifname, paramnames, prefix)
                else:
                    self.gh_export(ctx, ifname, paramnames, prefix)
            except:
                # The interface itself has not been saved. Undo any
                # kind, kindbind, term, and assertion additions.
                if cmd_hist is not None:
                    undo = cmd_hist[-1]
                    self.import_undo(undo[1], undo[2], undo[3], undo[4])
                    cmd_hist[-1] = None
                raise
            return

        if cmd in ('stmt', 'term', 'kind'):
            raise VerifyError("Interface file command '" + cmd +
                              "' occurred in proof file context.")
        else:
            msg = "Unknown command '" + cmd + "' in verify context."
            if self.fail_continue:
                out.write(msg)
            else:
                raise VerifyError(msg)

    def import_undo(self, k_undo, kb_undo, t_undo, s_undo):
        for label in s_undo:
            del self.syms[label]

        ix = len(t_undo)
        while ix > 0:
            ix -= 1
            termname = t_undo[ix]
            termix = self.terms[termname]
            assert(termix + 1 == len(self.term_hist))
            del self.terms[termname]
            del self.term_hist[-1:]
        for kname in kb_undo:
            del self.kinds[kname]
        for kname in k_undo:
            del self.kinds[kname]

    def undo_cmd(self):
        """ Undo the last command in this proof file context """
        cmd_hist = self.cmd_hist
        assert(cmd_hist is not None)
        n = len(cmd_hist) - 4
        assert(n >= 0 and (n & 3) == 0)
        cmd = cmd_hist[n]
        arg = cmd_hist[n + 1]
        #self.out.write('undo %s %s\n' % (cmd, arg[0]))
        data = cmd_hist[n + 3]
        del cmd_hist[n:]
        if isinstance(data, ErrorMark):
            self.error_count -= 1
            data = data.undo_info
            if cmd in ('thm', 'defthm'):
                if (isinstance(arg, list) and len(arg) > 0 and
                    isinstance(arg[0], basestring)):
                    label = arg[0]
                    l = self.badthms[label]
                    assert(l[-1] == n)
                    del l[-1]
                    if len(l) == 0:
                        del self.badthms[label]
        if data is None:
            return
        if cmd == 'thm':
            label = data
            del self.syms[label]
        elif cmd == 'defthm':
            label, termname = data
            del self.syms[label]
            termix = self.terms[termname]
            assert(termix + 1 == len(self.term_hist))
            del self.terms[termname]
            del self.term_hist[termix:]
        elif cmd in ('var', 'tvar'):
            vars = data
            for v in vars:
                del self.syms[v]
        elif cmd == 'kindbind':
            kname = data
            del self.kinds[kname]
            assert(self.kindbinds[-1] == kname)
            del self.kindbinds[-1:]
        elif cmd in ('import', 'export'):
            ifname, k_undo, kb_undo, t_undo, s_undo = data
            ifindex = self.interfaces[ifname]
            assert (ifindex + 1 == len(self.iflist))
            del self.interfaces[ifname]
            del self.iflist[-1:]
            self.import_undo(k_undo, kb_undo, t_undo, s_undo)
        else:
            assert(False)

    def check_proof(self, label, fv, hyps, stmt, proof,
                    dkind=None, dsig=None):
        if type(label) != type('label') or \
           type(fv) != type([]) or \
           type(hyps) != type([])or \
           (dkind is not None and (type(dkind) != type('kind') or \
                                   type(dsig) != type([]))):
            begin = 'thm (LABEL'
            if not dkind is None:
                begin = 'defthm (LABEL KIND (DEFSYM VAR ...)'
            raise SyntaxError('Expected ' + begin +
                 ' ((TVAR BVAR ...) ...) ({HYPNAME HYP} ...) CONC STEP ...)')
            
        if len(hyps) & 1:
            raise VerifyError('hyp list must have even length')

        varlist = []
        varmap = {}

        if dkind is not None:
            dt = term_common(dkind, dsig, None,
                            self.kinds, self.terms, self.syms)
            # Check that the term does not have two formal binding variable
            # arguments of the same kind.  Such arguments could be substituted
            # with the same actual binding variable argument, yet the
            # definition statement cannot say anything about the definition
            # in that case as its proof assumes all binding variables are
            # distinct. A bit ugly.
            tk, ak, fm = dt
            for j in xrange(1, len(fm)):
                if fm[j] < 0:
                    continue    # not a binding variable
                for i in xrange(j):
                    if fm[i] < 0:
                        continue
                    if ak[i] == ak[j]:
                        raise VerifyError('Formal binding arguments %s and %s of defined term %s have the same kind.' % (dsig[i+1], dsig[j+1], dsig[0]))

        hypmap = {}
        ihyps = []
        for i in range(0, len(hyps), 2):
            if not isinstance(hyps[i], basestring):
                raise VerifyError('hyp label must be string')
            if hyps[i] in hypmap:
                raise VerifyError('Repeated hypothesis label ' + hyps[1])
            e = self.internalize(hyps[i + 1], varlist, varmap)
            # e is (kw, kindix, iexp)
            ihyps.append(e[2])
            hypmap[hyps[i]] = e[2]
        num_hypvars = len(varlist)
        if dkind is not None:
            # Temporarily add the definition to self.terms when parsing the
            # conclusion. term_common checked that the term doesn't exist yet.
            termix = len(self.term_hist)
            self.terms[dsig[0]] = termix
            self.term_hist.append((dsig[0], -1, termix,
                                   dt[0], dt[1], dt[2], dsig, label))
        try:
            iconcl = self.internalize(stmt, varlist, varmap)[2]
        finally:
            if dkind is not None:
                # The term being defined must not occur in the hypotheses
                # or the proof steps. Note, however, that we leave the
                # term in term_hist.
                # It will be cleaned up by do_cmd() if anything fails
                # (or failed...)
                del self.terms[dsig[0]]
        num_nondummies = len(varlist)
        # fvmap will map the indices of binding variables occurring in the
        # hypotheses or conclusions to dictionaries (treated as sets)
        # indicating which term variables each binding variable may not
        # occur free in.  That is, if there is a free variable constraint
        # context (tvar bvar), then fvmap[ix(bvar)][ix(tvar)] is set to zero,
        # simply to add ix(tvar) into the domain of fvmap[ix(bvar)].
        # We could alternatively use a Python 2.4+ Set for each fvmap[bvar]...
        fvmap = {}
        for ix in xrange(num_nondummies):
            if varlist[ix][0] == 'var':
                fvmap[ix] = {}
        ifv = []
        for clause in fv:
            if not isinstance(clause, list) or len(clause) == 0:
                raise VerifyError('each fv clause must be list of vars')
            try:
                iclause = [varmap[vn] for vn in clause]
            except TypeError:
                raise VerifyError('Var in fv clause must be string')
            except KeyError:
                raise VerifyError('"%s" is not a variable occurring in the hypotheses or conclusions.' % vn)

            tvar = iclause[0]
            if varlist[tvar][0] != 'tvar':
                raise VerifyError('First var in fv clause must be tvar: %s'
                                  % clause[0])
            for bvix in iclause[1:]:
                if varlist[bvix][0] != 'var':
                    raise VerifyError('Subsequent vars in fv clause must be binding variables: %s'
                                      % varlist[bvix][2])
                fvmap[bvix][tvar] = 0
            ifv.append(iclause)

        proofctx = ProofCtx(label, ifv, ihyps, iconcl,
                            varlist, varmap, num_hypvars, num_nondummies,
                            fvmap)
        if dkind is not None:
            proofctx.defterm = dt

        for step in proof:
            #print 'step:', step
            if step == '?':
                for x in proofctx.stack:
                    print self.iexp_to_string(x, varlist)
                continue
            try:
                self.check_proof_step(hypmap, step, proofctx)
            except VerifyError, x:
                x.why += ' [' + sexp_to_string(step) + ']'
                x.proofctx = proofctx
                raise x
        if len(proofctx.mandstack) != 0:
            raise VerifyError('extra mand hyps on stack at and of proof',
                              label, proofctx)
        if len(proofctx.stack) != 1:
            raise VerifyError('stack must have one term at end of proof',
                              label, proofctx)
        extra = ''
        missing = ''
        for v in fvmap:
            for A, val in fvmap[v].iteritems():
                # Note, val = fvmap[v][A] may be:
                #   0, if the constraint (A v) was provided but not needed
                #   None, if the constraint was not provided, but was needed
                #   1, if the constraint was provided and needed
                if val == 0:
                    extra = extra + (' (%s %s)' %
                                     (varlist[A][2], varlist[v][2]))
                elif val is None:
                    missing = missing + (' (%s %s)' %
                                     (varlist[A][2], varlist[v][2]))

        if missing != '':
            raise VerifyError('Missing free variable constraint pairs:%s' %
                              missing)
        if extra != '':
            raise VerifyError('Extra free variable constraint pairs:%s' %
                              extra)

        # The caller checks the conclusion differently depending on whether
        # this is a thm or a defthm.
        return proofctx

    # These are really methods of both the verify and proofctx objects, and
    # are here by tradition.
    def check_proof_step(self, hypmap, step, proofctx):
        pvl = proofctx.varlist
        if isinstance(step, list):
            proofctx.mandstack.append(self.internalize(step, pvl,
                                                       proofctx.varmap))
            return

        if hypmap.has_key(step):
            if len(proofctx.mandstack) != 0:
                raise VerifyError('hyp expected no mand hyps, got %d' % len(proofctx.mandstack))
            proofctx.stack.append(hypmap[step])
            return

        try:
            v = self.syms[step]
        except KeyError:
            raise VerifyError('unknown proof step: ' + step)
        if v[0] in ('var', 'tvar'):
            proofctx.mandstack.append(self.internalize(step, pvl,
                                                       proofctx.varmap))
            return

        # v[0] is in ('stmt', 'thm', 'defthm')
        # Does the slicing get optimized away here?
        (fv, hyps, concl, varlist, num_hypvars, num_nondummies) = v[1:7]
        num_wild = num_nondummies - num_hypvars
        if len(proofctx.mandstack) != num_wild:
            raise VerifyError('expected %d mand hyps, got %d' %
                              (num_wild, len(proofctx.mandstack)))
        env = [-1]*num_nondummies
        try:
            for i in xrange(num_wild):
                e1 = i + num_hypvars
                wvar = varlist[e1]
                # wvar is (kw, kindix, vname)
                # Each element on mandstack is a triple (t, kindix, iexpr)
                # where t is 'tvar' or 'var' or 'term', kindix is the
                # epression's kind index, and iexpr is the actual internal
                # value on the stack.
                el = proofctx.mandstack[i]
                if el[1] != wvar[1]: # is this ok given kindbind?
                    raise VerifyError(
                        'kind mismatch for %s: expected %s, got %s' %
                        (wvar[2], self.kind_hist[wvar[1]][0],
                         self.kind_hist[el[1]][0]))
                e2 = el[2]
                match(e1, e2, env)

            sp = len(proofctx.stack) - len(hyps)
            if sp < 0:
                raise VerifyError('stack underflow')
            for i in range(len(hyps)):
                e1 = hyps[i]
                e2 = proofctx.stack[sp + i]
                match(e1, e2, env)

        except UnifyError, x:
            why = ('Unification error: %s vs %s (inside %s vs %s)' %
                   (self.iexp_to_string(x.e1, varlist),
                    self.iexp_to_string(x.e2, pvl),
                    self.iexp_to_string(e1, varlist),
                    self.iexp_to_string(e2, pvl)))
            raise VerifyError(why)

        invmap = {}
        for var in xrange(num_nondummies):
            exp = env[var]
            if varlist[var][0] == 'var':
                if isinstance(exp, list) or pvl[exp][0] != 'var':
                    raise VerifyError(
                        'Expected binding variable for %s but matched %s' %
                        (varlist[var][2],
                         self.iexp_to_string(exp, pvl)))
                if exp in invmap:
                    raise VerifyError(
                            'Binding variables %s and %s both map to %s' %
                            (varlist[invmap[exp]][2], varlist[var][2],
                             pvl[exp][2]))
                invmap[exp] = var
        for clause in fv:
            tvar = clause[0]
            for var in clause[1:]:
                if self.check_free_in_proof(env[var], env[tvar],
                                            proofctx):
                    raise VerifyError(
                            'Free variable constraint violation: Variable %s occurs explicitly free in %s'
                            % (pvl[env[var]][2], pvl[env[tvar]][2]))
        result = apply_subst(concl, env)
        #print 'result=', result, self.iexp_to_string(result, proofctx.varlist)
        proofctx.stack[sp:] = [result]
        proofctx.mandstack = []

    def def_conc_match(self, conc, remnant, dsig, freemap, proofctx, result):
        """ Check that the defthm conclusion <conc> properly matches the
            remnant expression <remnant> on the proof stack.
            <conc> and <remnant> are known to be well-formed internal
            expressions at this point. dsig is also internal.
        """
        if not isinstance(conc, list):
            if conc != remnant:
                raise VerifyError('Conclusion variable %s vs remnant %s ' %
                                  (proofctx.varlist[conc][2],
                                   self.iexp_to_string(remnant,
                                                       proofctx.varlist)))
            return
        if not isinstance(remnant, list):
            raise VerifyError('Expected term expression, found %s' %
                              proofctx.varlist[remnant][2])
        if conc[0] == remnant[0]:
            i = 1
            for arg in conc[1:]:
                self.def_conc_match(arg, remnant[i], dsig,
                                    freemap, proofctx, result)
                i = i + 1
            return

        # All uses of the new term must exactly match the term signature.
        if conc != dsig:
            raise VerifyError('Conclusion subexpression %s\nmatches neither remnant subexpression nor the new term signature %s\n exactly' %
                              (self.iexp_to_string(conc, proofctx.varlist),
                               self.iexp_to_string(dsig, proofctx.varlist)))

        if result[0] is not None:
            if remnant != result[0]:
                raise VerifyError('Non-identical expansions for new term')
            return

        # This is our first encounter with the term being defined in
        # the conclusion.
        result[0] = remnant

        # Check that every formal argument variable occurs in the definiens,
        # that any definition dummy variable in the definiens is also a proof
        # dummy, and that (for now) every definition dummy is a binding
        # variable that does not occur free in the definiens.  Note that
        # we assume a proof dummy may not occur free in any other variable.

        allv = self.allvars(remnant) #ugh
        i = 0
        for v in allv:
            if v in dsig[1:]:
                i = i + 1  # Note, each v occurs only once in allv...
                continue
            vv = proofctx.varlist[v]
            if v < proofctx.num_nondummies:
                raise VerifyError("Definition dummy '%s' is not a proof dummy."
                                  % vv[2])
            if vv[0] != 'var':
                raise VerifyError(
                    "Definition dummy '%s' is not a binding variable" % vv[2])
            if self.check_free_in(v, remnant, None, proofctx.varlist):
                raise VerifyError(
                    "Definition dummy '%s' occurs explicitly free in definiens"
                    % vv[2])

        if i != len(dsig) - 1:
            raise VerifyError(
                'Not all term argument variables occur in definiens')

        # Also need to construct the freemap for the new term.
        nargs = len(freemap)
        for i in xrange(nargs):
            bmap = freemap[i]
            if bmap < 0:
                continue  # skip term variables
            l = []
            # IDEA: make self.freelist() return a bitmap?
            self.freelist(conc[i + 1], remnant, l, proofctx.varlist)
            for j in xrange(nargs):
                if conc[j + 1] in l:
                    bmap = bmap | (1 << j)
            freemap[i] = bmap

    def check_free_in_proof(self, var, term, proofctx):
        # Note that if var is a proof dummy variable, then
        # proofctx.fvvarmap.get(var, None) is just None and
        # check_free_in() will return False unless var occurs _explicitly_
        # free in term.
        self.check_free_in(var, term, proofctx.fvvarmap.get(var, None),
                           proofctx.varlist)

def term_common(kindname, sig, freespecs, kinds, terms, syms):
    """ term parsing support for 'term' and 'defthm' commands """
    if not isinstance(sig, list) or len(sig) < 1 or \
       not isinstance(sig[0], basestring):
        raise SyntaxError(\
            'A term signature must be a list starting with a term symbol.')
    try:
        kind = kinds[kindname]
    except KeyError:
        raise VerifyError('Unknown kind ' + kindname)
    except TypeError:
        raise SyntaxError('A term kind name must be an atom.')
                            
    termname = sig[0]
    if termname in terms:
        raise VerifyError('A term ' + termname + ' already exists.')

    argkinds = []
    # freemap will be a list whose length is the number of arguments
    # of the term. If freemap[i] < 0, then argument i is a term variable
    # argument.  If freemap[i] >= 0, then argument i is a binding variable
    # and freemap[i] is a bitmap value. For 0 <= j < len(freemap), the jth
    # bit in freemap[i] is 1 if, in a term expression built from the term,
    # the actual binding variable argument i occurs free in the term expression
    # if it occurs free in the actual argument expression substituted for
    # argument j.
    invmap = {}
    args = sig[1:]
    nargs = len(args)
    freemap = [-1]*nargs
    for i in xrange(nargs):
        v = args[i]
        try:
            var = syms[v]
        except KeyError:
            raise VerifyError('Unknown variable ' + v)
        except TypeError:
            raise SyntaxError('Term formal argument must be variable')
        if v in invmap:
            raise VerifyError('Formal argument ' + v + ' reused')
        invmap[v] = i
        argkinds.append(var[1])  # kinds[var[1]] ?
        if var[0] == 'var':
            freemap[i] = 0      # empty bitmap by default
        elif var[0] != 'tvar':  # might be 'stmt' or 'thm' in defthm case
            raise VerifyError('Term formal argument must be a variable.')

    if freespecs is None:
        return (kind, argkinds, freemap)

    for freespec in freespecs:
        if not isinstance(freespec, list) or len(freespec) < 2:
            raise SyntaxError('Each free variable map must be a list of at least two variables.')
        try:
            bvix = invmap[freespec[0]]
        except KeyError:
            raise VerifyError(freespec[0] +
                              ' is not a formal argument variable')
        except (IndexError, TypeError):
            raise SyntaxError('A free variable specification must be a list of formal argument variables, the first of which is a binding variable')

        bmap = freemap[bvix]
        if bmap < 0:
            raise VerifyError(freespec[0] +
                              ' is not a binding variable argument')
        if bmap != 0:
            raise VerifyError('More than one freespec for ' + freespec[0])

        for x in freespec[1:]:
            try:
                ix = invmap[x]
            except TypeError:
                raise SyntaxError('Expected a variable, found ' +
                                  sexp_to_string(x) +
                                  ' in free variable specification list')
            except KeyError:
                raise VerifyError('Expected an argument variable, found ' +
                                  x + ' in free variable specification list ')
            po2 = (1 << ix)
            if (bmap & po2) != 0:
                # Might as well be strict here...
                raise VerifyError(\
                    'Duplicate argument variable listed in freespec for ' +
                    freespec[0])
            bmap = bmap | po2

        freemap[bvix] = bmap

    return (kind, argkinds, freemap)

    
def invertible_match(newexp, origexp, env, inv):
    if type(newexp) == type('var'):
        if type(origexp) != type('var'):
            return False
        v = env.get(newexp, None)
        if v != None:
            return (v == origexp)
        env[newexp] = origexp
        if origexp in inv:
            return False
        inv[origexp] = newexp
        return True
    if type(origexp) != type([]):
        return False
    # Note, we know that the arities are equal since this function is
    # called only with well-formed expressions. However, for robustness:
    n = len(newexp)
    if n != len(origexp) or n == 0:
        return False
    if newexp[0] != origexp[0]:
        return False
    i = 1
    for ne in newexp[1:]:
        if not invertible_match(ne, origexp[i], env, inv):
            return False
        i = i + 1
    return True

# name, verify, prefix, params, and sort refer to the interface
# as imported (or exported) into a Verify context, not to the interface
# itself.


class InterfaceCtx(GhilbertCtx):
    def __init__(self, global_ctx, fname):
        GhilbertCtx.__init__(self, global_ctx, fname)

    def param(self, ifname, pif, paramnames, prefix):
        subparams = []
        for pn in paramnames:
            try:
                subparams.append(self.interfaces[pn])
            except KeyError:
                raise VerifyError('Unknown interface parameter name ' + pn)
            except TypeError:
                raise SyntaxError('param parameter must be interface name')

        # The subparams check needs thought -- a parameter is not just
        # an InterfaceCtx, but an association of an InterfaceCtx with
        # a prefix and some subparameters of its own...
        # note, this check also checks distinctness of subparams
        # Are these parameter checks sufficient here?
        if len(subparams) != len(pif.iflist):
            raise VerifyError("Parameters to interface '%s' do not match."
                              % ifname)
        for ix in xrange(len(subparams)):
            ppif = self.iflist[subparams[ix]]
            if ppif[1] is not pif.iflist[ix][1]:
                raise VerifyError(
                    "Parameters to interface '%s' do not match." % ifname)

        kindmap = self.iface_kinds(pif, subparams, prefix)

        if self.cmd_hist is None:
            term_undo_list = None
        else:
            term_undo_list = self.cmd_hist[-1][3]
        ifindex = len(self.iflist)
        for t in pif.term_hist:
            # t is (termname_in_pif, origin_ifindex_in_pif, origin_termix,
            #       rkindix, argkindixs, freemap, sig [, defthm_label])
            if t[1] >= 0:
                continue
            tpref = prefix + t[0]
            if tpref in self.terms:
                raise VerifyError("A term '%s' already exists" % tpref)
            my_rkind = kindmap[t[3]]
            my_argkinds = [kindmap[kix] for kix in t[4]]
            n = len(self.term_hist)
            self.terms[tpref] = n
            self.term_hist.append((tpref, ifindex, t[2],
                                       my_rkind, my_argkinds, t[5], t[6]))
            if term_undo_list is not None:
                term_undo_list.append(tpref)

        self.interfaces[ifname] = ifindex
        self.iflist.append((ifname, pif, subparams, prefix, kindmap))
        

    # do_cmd() for InterfaceCtx
    def do_cmd(self, cmd, arg, record=None):
        cmd_hist = self.cmd_hist
        if cmd_hist is not None:
            cmd_hist.append(cmd)
            cmd_hist.append(arg)
            cmd_hist.append(record)
            cmd_hist.append(None)
        out = self.out
        if cmd == 'kind':
            if not isinstance(arg, list) or len(arg) != 1 or \
                   not isinstance(arg[0], basestring):
                raise SyntaxError("Expected 'kind (KINDNAME)'")
            kname = arg[0]
            if kname in self.kinds:
                raise VerifyError("A kind '%s' already exists." % arg)
            n = len(self.kind_hist)
            self.kinds[kname] = n
            self.kind_hist.append((kname, -1, n))
            if cmd_hist is not None:
                cmd_hist[-1] = kname
            return
        if cmd in ('var', 'tvar'):
            if not isinstance(arg, list) or len(arg) < 1 or \
               not isinstance(arg[0], basestring):
                raise SyntaxError("Expected 'var (KINDNAME VARNAME ...)'")
            kname = arg[0]
            kix = self.get_kind(kname)
            if cmd_hist is not None:
                cmd_hist[-1] = []
            for vn in arg[1:]:
                if not isinstance(vn, basestring):
                    raise SyntaxError("A variable must be an identifier: %s" %
                                      sexp_to_string(vn))
                if vn in self.syms:
                    raise VerifyError("A symbol '%s' already exists." % vn)
                self.syms[vn] = (cmd, kix, vn) # don't store kname for interface
                if cmd_hist is not None:
                    cmd_hist[-1].append(vn)
            return
        if cmd == 'term':
            if not isinstance(arg, list) or len(arg) < 2:
                raise SyntaxError("Expected 'term (KIND (TERMNAME VAR ...) (BVAR FVAR ...) ...)'")
            sig = arg[1]
            t = term_common(arg[0], sig, arg[2:],
                            self.kinds, self.terms, self.syms)
            
            n = len(self.term_hist)
            self.terms[sig[0]] = n
            self.term_hist.append((sig[0], -1, n,
                                   t[0], t[1], t[2], sig))
            if cmd_hist is not None:
                cmd_hist[-1] = sig[0]
            return
        if cmd == 'stmt':
            # InterfaceCtx stmt command handling
            if not isinstance(arg, list) or len(arg) != 4:
                raise SyntaxError('stmt needs exactly 4 arguments')
            (label, fv, hyps, concl) = arg
            if not isinstance(label, basestring) or \
               not isinstance(fv, list) or not isinstance(hyps, list):
                raise SyntaxError('Expected stmt (LABEL ((TVAR BVAR ...) ...) (HYP ...) CONCLUSION)')

            varlist = []
            varmap = {}
            ihyps = [self.internalize(hyp, varlist, varmap)[2] for hyp in hyps]
            num_hypvars = len(varlist)
            iconcl = self.internalize(concl, varlist, varmap)[2]

            ifv = []
            for clause in fv:
                if not isinstance(clause, list) or len(clause) < 2:
                    raise SyntaxError('Free variable contraint context clause must be a list of at least two variables')
                want = 'tvar'
                fvc = []
                for vname in clause:
                    try:
                        vix = varmap[vname]
                    except KeyError:
                        raise VerifyError("Free variable constraint context item '%s' is not a variable occurring in the hypotheses or conclusion." % vname)
                    except TypeError:
                        raise SyntaxError('Free variable constraint context clause items must be variables')
                    v = varlist[vix]
                    if v[0] != want:
                        raise VerifyError('In free variable constraint context clause %s, the first variable must be a term variable and the remaining variables must be binding variables' % sexp_to_string(clause))
                    want = 'var'
                    fvc.append(vix)
                ifv.append(fvc)

            cmd_ix = (None if cmd_hist is None else len(cmd_hist) - 4)
            self.add_sym(label,
                         ('stmt', ifv, ihyps, iconcl,
                          varlist, num_hypvars, len(varlist), cmd_ix))
            if cmd_hist is not None:
                cmd_hist[-1] = label
            return

        if cmd == 'param':
            if not isinstance(arg, list) or len(arg) != 4:
                raise SyntaxError( \
                    'Expected param (IFACE URL (PARAM ...) PREFIX)')
            ifname = arg[0]
            url = arg[1]            # Unused except to check it is an atom
            paramnames = arg[2]
            prefix = arg[3]
            if not isinstance(ifname, basestring) or \
               not isinstance(url, basestring) or \
               not isinstance(paramnames, list) or \
               not isinstance(prefix, basestring):
                raise SyntaxError( \
                    'Expected param (IFACE IGNORED_URL (PARAM ...) PREFIX)')
            if len(prefix) < 2 or prefix[0] != '"' or prefix[-1] != '"':
                raise SyntaxError('Enclose Namespace prefix in quotes.')
            prefix = prefix[1:-1]
            if ifname in self.interfaces:
                raise VerifyError(
                    "Interface parameter '%s' was already used." % ifname)

            # Fetch the interface by its url, it may already be loaded.
            # (It would be if this is an import or export context loaded
            # from a verify context)
            pif = self.global_ctx.fetch_interface(url, self)

            if cmd_hist is not None:
                # ifname, kinds, kindbinds, terms
                cmd_hist[-1] = [ifname, [], [], []]
            try:
                self.param(ifname, pif, paramnames, prefix)
            except:
                if cmd_hist is not None:
                    undo = cmd_hist[-1]
                    self.param_undo(undo[1], undo[2], undo[3])
                    cmd_hist[-1] = None
                raise
            return

        if cmd == 'kindbind':
            # We allow kindbind in interface files with the same semantics
            # as in proof files -- i.e., kindbind introduces a new kind
            # name as an alias for an existing kind. It does not join
            # two pre-existing kinds.
            self.kindbind_cmd(arg)
            if cmd_hist is not None:
                cmd_hist[-1] = arg[1]
            return
            
        out.write('*** Warning: unrecognized command ' + cmd + \
                  ' seen in import context. ***\n')

    def param_undo(self, k_undo, kb_undo, t_undo):
        ix = len(t_undo)
        while ix > 0:
            ix -= 1
            termname = t_undo[ix]
            #self.out.write('param_undo term %s' % termname)
            termix = self.terms[termname]
            assert(termix + 1 == len(self.term_hist))
            del self.terms[termname]
            del self.term_hist[-1:]
        for kname in kb_undo:
            #self.out.write('param_undo kind_bind %s' % kname)
            del self.kinds[kname]
        for kname in k_undo:
            #self.out.write('param_undo kind %s' % kname)
            del self.kinds[kname]

    def undo_cmd(self):
        """ Undo the last command in this interface file context """
        cmd_hist = self.cmd_hist
        assert(cmd_hist is not None)
        n = len(cmd_hist) - 4
        assert(n >= 0 and (n & 3) == 0)
        cmd = cmd_hist[n]
        arg = cmd_hist[n + 1]
        #self.out.write('undo %s %s\n' % (cmd, arg[0]))
        data = cmd_hist[n + 3]
        del cmd_hist[n:]
        if isinstance(data, ErrorMark):
            self.error_count -= 1
            data = data.undo_info
        if data is None:
            return
        if cmd == 'stmt':
            label = data
            del self.syms[label]
        elif cmd == 'term':
            termname = data
            termix = self.terms[termname]
            assert(termix + 1 == len(self.term_hist))
            del self.terms[termname]
            del self.term_hist[termix:]
        elif cmd in ('var', 'tvar'):
            vars = data
            for v in vars:
                del self.syms[v]
        elif cmd == 'kind':
            kname = data
            kix = self.kinds[kname]
            assert(kix + 1 == len(self.kind_hist))
            del self.kinds[kname]
            del self.kind_hist[-1]
        elif cmd == 'kindbind':
            kname = data
            del self.kinds[kname]
            assert(self.kindbinds[-1] == kname)
            del self.kindbinds[-1:]
        elif cmd == 'param':
            ifname, k_undo, kb_undo, t_undo = data
            ifindex = self.interfaces[ifname]
            assert (ifindex + 1 == len(self.iflist))
            del self.interfaces[ifname]
            del self.iflist[-1:]
            self.param_undo(k_undo, kb_undo, t_undo)
        else:
            assert(False)

if __name__ == '__main__':
    i = 1
    fail_continue = False
    verbosity = 1
    while i < len(sys.argv):
        arg = sys.argv[i]
        if arg[0] != '-':
            break
        if arg == '--':
            i = i + 1
            break
        if arg == '-c':
            fail_continue = True
            break
        if arg == '-v':
            i = i + 1
            verbosity = int(sys.argv[i])
        else:
            print >> sys.stderr, 'Unknown option:', arg
        i = i + 1
        
    fn = sys.argv[i]
    urlctx = UrlCtx('', fn, sys.stdin)
    #urlctx.out = sys.stdout
    if fn == '-':
        url = fn
    else :
        url = 'file://' + fn
    norm_url = urlctx.normalize(url, fn)
    gctx = GlobalCtx(urlctx)
    vctx = VerifyCtx(gctx, norm_url, fail_continue)
    vctx.verbosity = verbosity
    scanner = urlctx.resolve(url, fn)
    gctx.run(scanner, url, vctx)
    if vctx.error_count != 0:
        print 'Number of errors: %d' % vctx.error_count
        sys.exit(1)

