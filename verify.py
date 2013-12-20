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

class VerifyError(Exception):
    def __init__(self, why, label = None, stack = None):
        self.why = why
        self.label = label
        self.stack = stack
        self.step = None

class Scanner:
    def __init__(self, instream):
        self.instream = instream
        self.lineno = 0
        self.toks = []
        self.tokix = 0
    def get_tok(self):
        while len(self.toks) == self.tokix:
            if self.instream == None:
                return None
            line = self.instream.readline()
            self.lineno += 1
            if line == '':
                return None
            line = line.split('#')[0]
            line = line.replace('(', ' ( ')
            line = line.replace(')', ' ) ')
            self.toks = line.split()
            self.tokix = 0
        result = self.toks[self.tokix]
        self.tokix += 1
        return result

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
        self.repobase = repobase
        self.base = os.path.split(basefn)[0]
        self.instream = instream
    def resolve(self, url):
        # need to be careful about security if used on malicious inputs
        if url.startswith('file://'):
            fn = url[7:]
        elif url.startswith('/'):
            fn = os.path.join(self.repobase, url[1:])
        elif url == '-':
            return self.instream
        else:
            fn = os.path.join(self.base, url)
        return open(fn,'r')

class ProofCtx:
    def __init__(self, label, fvvarmap):
        self.label = label
        self.stack = []
        self.mandstack = []
        self.fvvarmap = fvvarmap
        self.defterm = None

class VerifyCtx:
    # error_handler(label, msg) -> true means continue
    def __init__(self, urlctx, run, error_handler = None):
        self.kinds = {}
        self.terms = {}
        self.syms = {}
        self.interfaces = {}
        self.urlctx = urlctx
        self.run = run
        self.error_handler = error_handler
    def add_sym(self, label, val):
        if self.syms.has_key(label):
            raise VerifyError('Symbol ' + label + ' already defined')
        self.syms[label] = val
    def add_kind(self, kind, val):
        if self.kinds.has_key(kind):
            raise VerifyError('Kind ' + kind + ' already defined')
        self.kinds[kind] = val
    def get_kind(self, kind):
        try:
            return self.kinds[kind]
        except KeyError:
            raise VerifyError('Kind not known: ' + kind)
    def add_term(self, label, kind, argkinds, freemap):
        if self.terms.has_key(label):
            raise VerifyError('Term ' + label + ' already defined')
        #print 'add_term ', label, (kind, argkinds, freemap)
        self.terms[label] = (kind, argkinds, freemap)
    def add_assertion(self, kw, label, fv, hyps, concl, varlist,
                      num_hypvars, num_nondummies, syms):
        mand = varlist[num_hypvars:num_nondummies]
        self.add_sym(label, (kw, fv, hyps, concl, mand, syms))

    def allvars(self, exp):
        fv = []
        self.allvars_rec(exp, fv)
        return fv
    def allvars_rec(self, exp, fv):
        if type(exp) == type('var'):
            if not exp in fv:
                fv.append(exp)
        elif type(exp) == type([]):
            for subexp in exp[1:]:
                self.allvars_rec(subexp, fv)

    def free_scan(self, var, term, accum):
        if type(term) == str:
            return accum(term)

        freemap = self.terms[term[0]][2]
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


    def free_in(self, var, term, fvvars):
        return self.free_scan(var, term,
            lambda v :
               (True if v == var or
                        (fvvars != None and
                         self.syms[v][0] == 'tvar' and
                         v not in fvvars)
                     else False))

    # Check if binding variable var occurs free in term.
    # This routine returns True if and only if var occurs _explicitly_ free
    # in fvvars.
    # If fvvars is not None, it is a dictionary. In that case, the domain of
    # fvvars consists of some term variables in the variable space of the
    # theorem being proved.
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
    def check_free_in(self, var, term, fvvars):
        def checker(v, var=var, fvvars=fvvars, syms=self.syms):
            if v == var:
                return True  # only stop scan if var explicitly free.
            if fvvars == None or syms[v][0] == 'var':
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

    def freelist(self, bvar, exp, l):
        """ Append to l the list of variables occurring in exp for which
            binding variable bvar might occur free in exp if it occurs
            free in one of the variables of the list.
        """
        def checker(v, bvar=bvar, l=l, syms=self.syms):
            if v != bvar and syms[v][0] == 'var':
                return False # different binding variables are distinct
            if v not in l:
                l.append(v)
            return False
        return self.free_scan(bvar, exp, checker)


    # Check well-formedness of the expression exp and return its kind.
    # Add the variables found to varlist and varmap: the former is a list
    # of items syms[v] for each variable v found, and varmap maps the names
    # of found variables to their indices in varlist.
    def kind_of(self, exp, varlist, varmap, syms, check_bv_expr = None):
        """ Check that exp is a well-formed expression, and return its kind """
        if isinstance(exp, basestring):
            try:
                v = syms[exp]
            except KeyError:
                raise VerifyError('Not a known variable: ' + exp)
            if v[0] not in ('var', 'tvar'):
                raise VerifyError('Symbol not a variable: ' + exp)
            if check_bv_expr is not None and v[0] != 'var':
                raise VerifyError(
                  'Expected a binding variable, but found a term variable: ' \
                    + exp + ' in ' + sexp_to_string(check_bv_expr))
            if not exp in varmap:
                varmap[exp] = len(varlist)
                varlist.append(v)
            return self.kinds[v[1]]

        # Else, exp is a list
        if check_bv_expr is not None:
            raise VerifyError('Expected a binding variable, but found a list: '
                  + sexp_to_string(exp) + ' in ' + sexp_to_string(check_bv_expr))
        if len(exp) == 0:
            raise VerifyError("term can't be empty list")
        if not isinstance(exp[0], basestring):
            raise VerifyError('term must be id, found ' +
                              sexp_to_string(exp[0]))
        try:
            term = self.terms[exp[0]]
        except KeyError:
            raise VerifyError('term ' + exp[0] + ' not known')
        # term is (kind, argkinds, freemap)
        if len(exp) - 1 != len(term[1]):
            #print exp, term
            raise VerifyError('arity mismatch: ' + exp[0] + ' has arity ' +
                              str(len(term[1])) + ' but was given ' +
                              str(len(exp) - 1) + ' arguments')
        for i in range(len(exp) - 1):
            check_bv_expr = None
            if term[2][i] >= 0:
                check_bv_expr = exp
            child_kind = self.kind_of(exp[i + 1], varlist, varmap,
                                      syms, check_bv_expr)
            if child_kind != self.kinds[term[1][i]]:
                #print self.kinds
                raise VerifyError('kind mismatch: ' + sexp_to_string(exp) +
                     ' wanted ' + self.kinds[term[1][i]] + ' found ' +
                                  child_kind)
        return self.kinds[term[0]]

    def do_cmd(self, cmd, arg, out):
        """ Command processing for Verify (proof file) context """
        if cmd == 'thm':
            # thm (LABEL ((TVAR BVAR ...) ...) ({HYPNAME HYP} ...) CONC
            #        STEP ...)
            if len(arg) < 5:
                raise VerifyError('Expected at least 5 args to thm')
            (label, fv, hyps, conc) = arg[:4]
            out.write('thm %s\n' % label)
            proof = arg[4:]
            try:
                proofctx, fvmap, hypmap = self.setup_proof(label, fv, hyps, conc)
            except VerifyError, x:
                msg = 'error in thm ' + label + ': '
                out.write(msg + '\n')
                if self.error_handler is not None: self.error_handler(label, x.why)
                raise x

            try:
                self.check_proof(proofctx, proof, fvmap, hypmap)
                if proofctx.stack[0] != conc:
                    raise VerifyError('\nwanted ' + sexp_to_string(conc), label,
                                      proofctx.stack)
            except VerifyError, x:
                msg = 'error in thm ' + label + ': '
                out.write(msg + '\n')
                if x.stack != None:
                    for i in xrange(len(x.stack)):
                        out.write('P' + str(i) + ': ' + sexp_to_string(x.stack[i]) + '\n')
                if self.error_handler is None or not self.error_handler(label, x.why):
                    raise x

            self.add_assertion('thm', label, fv, hyps[1::2], conc,
                               proofctx.varlist, proofctx.num_hypvars,
                               proofctx.num_nondummies, self.syms)
            return
        if cmd == 'defthm':
            # defthm (LABEL KIND (DEFSYM VAR ...)
            #           ((TVAR BVAR ...) ...) ({HYPNAME HYP} ...) CONC
            #           STEP ...)
            if len(arg) < 7:
                raise VerifyError('Expected at least 7 arguments to defthm')
            (label, dkind, dsig, fv, hyps, conc) = arg[:6]
            out.write('defthm %s\n' % label)
            proof = arg[6:]
            try:
                proofctx, fvmap, hypmap = self.setup_proof(label, fv, hyps, conc,
                                            dkind, dsig)
                self.check_proof(proofctx, proof, fvmap, hypmap)
            except VerifyError, x:
                out.write('Error in defthm ' + label + ': ' + x.why)
                if x.stack != None:
                    for i in xrange(len(x.stack)):
                        out.write('P' + str(i) + ': ' + sexp_to_string(x.stack[i]))
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
            remnant = proofctx.stack[0]
            result = [None]

            try:
                self.def_conc_match(conc, remnant, dsig,
                                    t, proofctx, result)
            except VerifyError, x:
                x.why = ('The defthm conclusion\n ' + sexp_to_string(conc) +
                         '\nfails to match remnant\n ' +
                         sexp_to_string(remnant) + '\n*** ' + x.why)
                raise
            if result[0] == None:
                raise VerifyError("The term '" + dsig[0] +
                   "' being defined does not occur in the defthm conclusion.")
            # out.write('New term ' + dsig[0], t)
            self.terms[dsig[0]] = t
            self.add_assertion('thm', label, fv, hyps[1::2], conc,
                               proofctx.varlist, proofctx.num_hypvars,
                               proofctx.num_nondummies, self.syms)
            return
        if cmd in ('var', 'tvar'):
            kind = self.get_kind(arg[0])
            for v in arg[1:]:
                self.add_sym(v, (cmd, kind, v))
            return
        if cmd == 'kindbind':
            self.add_kind(arg[1], self.get_kind(arg[0]))
            return
        if cmd in ('import', 'export'):
            # import (IFACE URL (PARAMS) PREFIX)
            if type(arg) != type([]) or len(arg) != 4:
                raise SyntaxError("Expected '" + cmd +
                                  " (IFACE URL (PARAM ...) PREFIX)'")
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
            # Check that the parameter interfaces are all distinct and all
            # correspond to existing interfaces.
            inverse = {}
            params = []
            for pn in paramnames:
                if pn in inverse:
                    raise VerifyError("Interface %s passed more than once to import context." % pn)
                inverse[pn] = 0
                try:
                    params.append(self.interfaces[pn])
                except KeyError:
                    raise VerifyError("Unknown interface %s" % pn)
                except TypeError:
                    raise SyntaxError("Non-atom provided as interface parameter.")

            if cmd == 'import':
                out.write('Importing %s\n' % ifname)
                ctx = ImportCtx(ifname, self, prefix, params)
            else:
                out.write('Exporting %s\n' % ifname)
                ctx = ExportCtx(ifname, self, prefix, params)
                
            if not self.run(self.urlctx, url, ctx, out):
                raise VerifyError (cmd + " of interface %s, URL %s" %
                                   (ifname, url))
                
            # Check that all passed interface parameters were in fact used.
            if len(ctx.used_params) != len(params):
                raise VerifyError(
                    "Some interface parameters were not used in the " + cmd +
                    " context.")

            # Don't need ctx.kinds or ctx.terms any more
            ctx.kinds = None
            ctx.terms = None
            self.interfaces[ifname] = ctx
            return

        if cmd in ('stmt', 'term', 'kind'):
            raise VerifyError("Interface file command '" + cmd +
                              "' occurred in proof file context.")
        else:
            msg = "Unknown command '" + cmd + "' in verify context."
            if self.error_handler is None or not self.error_handler('', msg):
                raise VerifyError(msg)
            else:
                out.write(msg)

    def setup_proof(self, label, fv, hyps, stmt,
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

        # fvmap will map the names of binding variables occurring in the
        # hypotheses or conclusions to dictionaries (treated as sets)
        # indicating which term variables each binding variable may not
        # occur free in.  That is, if there is a free variable constraint
        # context (tvar bvar), then fvmap[bvar][tvar] is set to zero, simply
        # to add tvar into the domain of fvmap[bvar].
        # We could alternatively use a Python 2.4+ Set for each fvmap[bvar]...
        fvmap = {}
        vall = []
        varmap = {}

        if dkind is not None:
            t = term_common(dkind, dsig, None,
                            self.kinds, self.terms, self.syms)
            # Check that the term does not have two formal binding variable
            # arguments of the same kind.  Such arguments could be substituted
            # with the same actual binding variable argument, yet the
            # definition statement cannot say anything about the definition
            # in that case as its proof assumes all binding variables are
            # distinct. A bit ugly.
            tk, ak, fm = t
            for j in xrange(1, len(fm)):
                if fm[j] < 0:
                    continue    # not a binding variable
                for i in xrange(j):
                    if fm[i] < 0:
                        continue
                    if ak[i] == ak[j]:
                        raise VerifyError('Formal binding arguments %s and %s of defined term %s have the same kind.' % (dsig[i+1], dsig[j+1], dsig[0]))

        hypmap = {}
        for i in range(0, len(hyps), 2):
            if not isinstance(hyps[i], basestring):
                raise VerifyError('hyp label must be string')
            if hyps[i] in hypmap:
                raise VerifyError('Repeated hypothesis label ' + hyps[1])
            hypmap[hyps[i]] = hyps[i + 1]
            self.kind_of(hyps[i + 1], vall, varmap, self.syms)
        num_hypvars = len(vall)
        if dkind is not None:
            # Temporarily add the definition to self.terms when parsing the
            # conclusion. term_common checked that the term doesn't exist yet.
            self.terms[dsig[0]] = t
        self.kind_of(stmt, vall, varmap, self.syms)
        if dkind is not None:
            # The term being defined must not occur in the hypotheses or the
            # proof steps.
            del self.terms[dsig[0]]
        num_nondummies = len(vall)
        for var in vall:
            if var[0] == 'var':
                fvmap[var[2]] = {}
        for clause in fv:
            if not isinstance(clause, list) or len(clause) == 0:
                raise VerifyError('each fv clause must be list of vars')
            tvar = clause[0]
            try:
                vi = varmap[tvar]
            except TypeError:
                raise VerifyError('var in fv clause must be string')
            except KeyError:
                raise VerifyError('"%s" is not a variable occurring in the hypotheses or conclusions.' % tvar)
            if vall[vi][0] != 'tvar':
                raise VerifyError('first var in fv clause must be tvar: ' + tvar)
            for var in clause[1:]:
                try:
                    vm = fvmap[var]
                except TypeError:
                    raise VerifyError('var in fv clause must be string')
                except KeyError:
                    raise VerifyError('subsequent var in fv clause must be a binding variable occurring in the hypotheses or conclusions: ' + var)
                vm[tvar] = 0

        proofctx = ProofCtx(label, fvmap)
        proofctx.varlist = vall
        proofctx.varmap = varmap
        proofctx.num_hypvars = num_hypvars
        proofctx.num_nondummies = num_nondummies
        if dkind is not None:
            proofctx.defterm = t
        return proofctx, fvmap, hypmap

    def check_proof(self, proofctx, proof, fvmap, hypmap):
        for step in proof:
            #print 'step:', step
            try:
                self.check_proof_step(hypmap, step, proofctx)
            except VerifyError, x:
                x.why += ' [' + sexp_to_string(step) + ']'
                x.stack = proofctx.stack
                raise x
        if len(proofctx.mandstack) != 0:
            raise VerifyError('extra mand hyps on stack at and of proof',
                              proofctx.label)
        if len(proofctx.stack) != 1:
            raise VerifyError('stack must have one term at end of proof',
                              proofctx.label, proofctx.stack)
        extra = ''
        missing = ''
        for v in fvmap:
            for A, val in fvmap[v].iteritems():
                if val == 0:
                    extra = extra + (' (%s %s)' % (A, v))
                elif val is None:
                    missing = missing + (' (%s %s)' % (A, v))

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
        if isinstance(step, list):
            kind = self.kind_of(step, proofctx.varlist,
                                proofctx.varmap, self.syms)
            #print 'kind of ' + sexp_to_string(step) + ' = ' + kind
            proofctx.mandstack.append(('tvar', kind, step))
        elif hypmap.has_key(step):
            if len(proofctx.mandstack) != 0:
                raise VerifyError('hyp expected no mand hyps, got %d' % len(proofctx.mandstack))
            proofctx.stack.append(hypmap[step])
        else:
            try:
                v = self.syms[step]
            except KeyError:
                raise VerifyError('unknown proof step: ' + step)
            if v[0] in ('var', 'tvar'):
                if not step in proofctx.varmap:
                    proofctx.varmap[step] = len(proofctx.varlist)
                    proofctx.varlist.append(v)
                proofctx.mandstack.append(v)
            elif v[0] in ('stmt', 'thm'):
                (fv, hyps, concl, mand, syms) = v[1:]
                if len(mand) != len(proofctx.mandstack):
                    raise VerifyError('expected %d mand hyps, got %d' % (len(mand), len(proofctx.mandstack)))
                env = {}
                for i in range(len(mand)):
                    tkind = mand[i]
                    # Each element on mandstack is a triple (t, kind, expr)
                    # where t is 'tvar' or 'var', kind is the epression's kind
                    # and expr is the actual value on the stack.
                    el = proofctx.mandstack[i]
                    if el[1] != tkind[1]: # is this ok given kindbind?
                        raise VerifyError('kind mismatch for ' + tkind[2] + ': expected ' + tkind[1] + ' got ' + el[1])
                    self.match(tkind[2], el[2], env)
                sp = len(proofctx.stack) - len(hyps)
                if sp < 0:
                    raise VerifyError('stack underflow')
                for i in range(len(hyps)):
                    el = proofctx.stack[sp + i]
                    self.match(hyps[i], el, env)
                invmap = {}
                for var, exp in env.iteritems():
                    if syms[var][0] == 'var':
                        if not isinstance(exp, basestring):
                            raise VerifyError('expected binding variable for ' +
                                              var + ' but matched ' +
                                              sexp_to_string(exp))
                        if self.syms[exp][0] != 'var':
                            raise VerifyError('expected binding variable for ' +
                                              var + '; ' + exp +
                                              ' is term variable')
                        if invmap.has_key(exp):
                            raise VerifyError('binding variables ' + invmap[exp] + ' and ' + var + ' both map to ' + exp)
                        invmap[exp] = var
                    exp_kind = self.kind_of_expression(exp)
                    if syms[var][0] == 'tvar' and syms[var][1] != exp_kind:
                        raise VerifyError('kind mismatch: ' + sexp_to_string(exp) +
                            ' wanted ' + syms[var][1] + ' found ' + exp_kind)

                for clause in fv:
                    tvar = clause[0]
                    for var in clause[1:]:
                        if self.check_free_in_proof(env[var], env[tvar],
                                                    proofctx):
                            raise VerifyError('Free variable constraint violation: Variable %s occurs explicitly free in %s' % (env[var], env[tvar]))
                #print 'env:', env, 'syms:', syms, 'invmap:', invmap
                result = self.apply_subst(concl, env)
                proofctx.stack[sp:] = [result]
                proofctx.mandstack = []
                #print 'stack:', proofctx.stack

    def kind_of_expression(self, expression):
        if expression.__class__ == 'v'.__class__:
            return self.syms[expression][1]
        else:
            return self.terms[expression[0]][0]

    def def_conc_match(self, conc, remnant, dsig, defterm, proofctx, result):
        """ Check that the defthm conclusion <conc> properly matches the
            remnant expression <remnant> on the proof stack.
            <conc> and <remnant> are known to be well-formed at this point.
        """
        if isinstance(conc, basestring):
            if conc != remnant:
                raise VerifyError('Conclusion variable ' + conc +
                                  ' vs. remnant ' + sexp_to_string(remnant))
            return
        if type(remnant) != type([]):
            raise VerifyError('Expected term expression, found ' + remnant)
        if conc[0] == remnant[0]:
            i = 1
            for arg in conc[1:]:
                self.def_conc_match(arg, remnant[i], dsig,
                                    defterm, proofctx, result)
                i = i + 1
            return

        # All uses of the new term must exactly match the term signature.
        if conc != dsig:
            raise VerifyError('Conclusion subexpression ' + \
                         sexp_to_string(conc) +
                         '\nmatches neither remnant subexpression nor the ' +
                         'new term signature ' + sexp_to_string(dsig) +
                         '\nexactly.')

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

            vi = proofctx.varmap[v]
            if vi < proofctx.num_nondummies:
                raise VerifyError("Definition dummy '" + v +
                                  "' is not a proof dummy.")
            vv = proofctx.varlist[vi]
            if vv[0] != 'var':
                raise VerifyError("Definition dummy '" + v +
                                  "' is not a binding variable")
            if self.check_free_in(v, remnant, None):
                raise VerifyError("Definition dummy '" + v +
                                  "' occurs explicitly free in definiens")

        if i != len(dsig) - 1:
            raise VerifyError(
                'Not all term argument variables occur in definiens')

        # Also need to construct the freemap for the new term.
        freemap = defterm[2]
        nargs = len(freemap)
        for i in xrange(nargs):
            bmap = freemap[i]
            if bmap < 0:
                continue  # skip term variables
            l = []
            # IDEA: make self.freelist() return a bitmap?
            self.freelist(conc[i + 1], remnant, l)
            for j in xrange(nargs):
                if conc[j + 1] in l:
                    bmap = bmap | (1 << j)
            freemap[i] = bmap

    def check_free_in_proof(self, var, term, proofctx):
        # Note that if var is a proof dummy variable, then
        # proofctx.fvvarmap.get(var, None) is just None and
        # check_free_in() will return False unless var occurs _explicitly_
        # free in term.
        return self.check_free_in(var, term, proofctx.fvvarmap.get(var, None))

    # match templ, which is an expression in the variable space of the
    # assertion being applied, against exp, an expression in the variable
    # space of the current proof, extending dictionary env, which maps from
    # the variables in the template space to expressions in the current proof
    def match(self, templ, exp, env):
        if type(templ) == type('var'):
            if env.has_key(templ):
                if exp != env[templ]:
                    # todo: more debug detail
                    raise VerifyError('Unification error')
            else:
                # Note, we check elsewhere if a binding variable is matched
                # against a non-binding-variable term.
                env[templ] = exp
        elif type(templ) == type([]):
            if type(exp) != type([]):
                raise VerifyError('Unification error, expected ' + sexp_to_string(templ) + ' got ' + exp)
            if templ[0] != exp[0]:
                raise VerifyError('Unification error, expected ' + templ[0] + ' got ' + exp[0])
            # todo: next check should never trigger, I think all terms
            # given to match are well-formed.
            if len(exp) != len(templ):
                raise VerifyError('Term ' + templ[0] + ' expects arity ' +
                                  str(len(templ)) + ' got ' + str(len(exp)))
            for i in range(1, len(templ)):
                self.match(templ[i], exp[i], env)

    def apply_subst(self, templ, env):
        if type(templ) == type('var'):
            return env[templ]
        elif type(templ) == type([]):
            return [templ[0]] + [self.apply_subst(el, env) for el in templ[1:]]

def term_common(kindname, sig, freespecs, kinds, terms, vars):
    """ term parsing support for 'term' and 'defthm' commands """
    if  type(sig) != type([]) or len(sig) < 1 or type(sig[0]) != type('term'):
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
            var = vars[v]
        except KeyError:
            raise VerifyError('Unknown variable ' + v)
        except TypeError:
            raise SyntaxError('Term formal argument must be variable')
        if v in invmap:
            raise VerifyError('Formal argument ' + v + ' reused')
        invmap[v] = i
        argkinds.append(var[1])  # kinds[var[1]] ?
        if var[0] == 'var':
            freemap[i] = 0      # empty bitmap
        elif var[0] != 'tvar':  # might be 'stmt' or 'thm' in defthm case
            raise VerifyError('Term formal argument must be a variable.')

    if freespecs is None:
        return (kind, argkinds, freemap)

    for freespec in freespecs:
        if type(freespec) != type([]) or len(freespec) < 2:
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

class InterfaceCtx:
    def __init__(self, name, verify, prefix, params, sort="import"):
        self.name = name
        self.verify = verify
        self.prefix = prefix
        self.params = params
        self.sort = sort
        self.used_params = {}
        self.vars = {}
        # self.myterm holds the terms introduced by this import context.
        # self.terms is the larger collection of terms visible at the
        # current point in this import context. It contains also terms
        # made available via param commands.
        self.terms = {}
        self.myterms = {}
        # self.mykinds is the collection of kinds introduced by the import
        # context itself. self.kinds is the larger collection of kinds
        # available to the import context(at the current point). It includes
        # also kinds made available via param commands.
        self.kinds = {}
        self.mykinds = {}
        self.error_handler = None

    def get_kind(self, rawkind):
        try:
            return self.kinds[rawkind]
        except KeyError:
            raise VerifyError('Kind ' + rawkind + ' is not known in ' + \
                              self.sort + ' context.')
        except TypeError:
            raise SyntaxError ('A kind name must be a string.')

    def kind_cmd_common(self, arg):
        if type(arg) != type([]) or len(arg) != 1:
            raise VerifyError('kind command takes one arg')
        kname = arg[0]
        if type(kname) != type('str'):
            raise VerifyError('kind argument must be string')

        if kname in self.kinds:
            raise VerifyError('A kind ' + kname +
                     ' is already visible in the current ' + self.sort +
                     ' export context.')

        kprefixed = self.prefix + kname

        self.kinds[kname] = kprefixed
        self.mykinds[kname] = kprefixed
        return kprefixed

    def var_cmd(self, cmd, arg):
        if not isinstance(arg, list) or len(arg) < 1:
            raise SyntaxError('Expected ' + cmd + ' (KIND VAR ...)')
        kind = self.get_kind(arg[0])
        for v in arg[1:]:
            if type(v) != type('var'):
                raise SyntaxError('Variable names must be atoms.')
            if v in self.vars:
                raise VerifyError('Variable ' + v + ' already defined')
            self.vars[v] = (cmd, kind, v)

    def param_cmd(self, arg):
        # param (IFACE IGNORED_URL (PARAM ...) PREFIX)
        if type(arg) != type([]) or len(arg) != 4:
            raise SyntaxError( \
                'Expected param (IFACE IGNORED_URL (PARAM ...) PREFIX)')
        ifname = arg[0]
        url = arg[1]            # Unused except to check it is an atom
        paramnames = arg[2]
        prefix = arg[3]
        if type(ifname) != type('ifname') or \
            type(url) != type('url') or \
            type(paramnames) != type([]) or \
            type(prefix) != type('prefix'):
            raise SyntaxError( \
                'Expected param (IFACE IGNORED_URL (PARAM ...) PREFIX)')
        if len(prefix) < 2 or prefix[0] != '"' or prefix[-1] != '"':
            raise SyntaxError('Namespace prefix must be enclosed in quotes')
        prefix = prefix[1:-1]

        if ifname in self.used_params:
            raise VerifyError('Interface parameter ' + ifname + \
                              ' was already used.')
        n = len(self.used_params)
        try:
            p = self.params[n]
        except IndexError:
            raise VerifyError(\
                "More param commands than provided interface parameters")

        subparams = []
        for pn in paramnames:
            try:
                subparams.append(self.used_params[pn])
            except KeyError:
                raise VerifyError('Unknown interface parameter name ' + pn)
            except TypeError:
                raise SyntaxError('param parameter must be interface name')

        # note, this check also checks distinctness of subparams
        if subparams != p.params:
            raise VerifyError('Context ' + self.name + \
                   ' changes parameters to parameter interface ' + \
                   ifname + ' (' + p.name + ')')

        self.used_params[ifname] = p

        # Make the param interface's kinds and terms available in
        # the current import context, with the specified prefix.
        # For each, verify that there is not already a kind or term in the
        # import context namespace with a colliding name.
        # Note that we don't add stmt's from the param interface
        # the current import context -- they are not needed.
        for k, kr in p.mykinds.iteritems():
            kpref = prefix + k
            if kpref in self.kinds:
                raise VerifyError('Context ' + self.name +
                                  ' already contains a kind ' + kpref)
            self.kinds[kpref] = kr
        for t, tr in p.myterms.iteritems():
            tpref = prefix + t
            if tpref in self.terms:
                raise VerifyError('Context ' + self.name +
                                  ' already contains a term ' + tpref)
            self.terms[tpref] = tr

class ImportCtx(InterfaceCtx):
    def __init__(self, name, verify, prefix, params):
        InterfaceCtx.__init__(self, name, verify, prefix, params, 'import')

    def map_syms(self, sexp, mapping, varlist, varmap,
                 kind=None, binding_var=False):
        """ Apply mapping to term symbols in an expression 'sexp'
            Check that the expression is well-formed, satisfying kind and
            binding constraints. Collect the variables used in used_vars.
        """
        if isinstance(sexp, basestring):
            try:
                v = self.vars[sexp]
            except KeyError:
                raise VerifyError(\
                    'Variable %s not known in import context' % sexp)
            if kind is not None and kind != v[1]:
                raise VerifyError('Expected expression of kind %s, found %s' %
                                  (kind, sexp))
            if binding_var and v[0] != 'var':
                raise VerifyError(\
                    'Expected a binding variable, found term variable %s' %
                    sexp)
            if sexp not in varmap:
                varmap[sexp] = len(varlist)
                varlist.append(v)
            return sexp

        if len(sexp) < 1 or type(sexp[0]) != type ('name'):
            raise SyntaxError('Invalid term expression ' +
                              sexp_to_string(sexp))
        if binding_var:
            raise VerifyError('Expected a binding variable, found %s' %
                              sexp_to_string(sexp))
        try:
            tmapped = mapping[sexp[0]]
            t = self.verify.terms[tmapped]
        except KeyError:
            raise VerifyError('Expression %s has unknown term symbol' %
                              sexp_to_string(sexp))
        # t is (kind, argkinds, freemap)
        if kind is not None and t[0] != kind:
            raise VerifyError('Expected expression of kind %s, found %s' %
                              (kind, sexp_to_string(sexp)))
        newterm = [tmapped]
        nargs = len(sexp) - 1
        if len(t[1]) != nargs:
            raise VerifyError('Arity mismatch for term expression %s' %
                              sexp_to_string(sexp))
        for j in xrange(len(sexp) - 1):
            el = sexp[j + 1]
            argkind = t[1][j]
            binding_var = t[2][j] >= 0
            newterm.append(self.map_syms(el, mapping, varlist, varmap,
                                         argkind, binding_var))
        return newterm

    def do_cmd(self, cmd, arg, out):
        """ Command processing for import context """
        if cmd == 'kind':
            kprefixed = self.kind_cmd_common(arg)
            self.verify.add_kind(kprefixed, kprefixed)
        elif cmd in ('var', 'tvar'):
            self.var_cmd(cmd, arg)
        elif cmd == 'term':
            if type(arg) != type([]) or len(arg) < 2:
                raise SyntaxError("Expected 'term (KIND (TERMNAME VAR ...) (BVAR FVAR ...) ...)'")
            t = term_common(arg[0], arg[1], arg[2:],
                            self.kinds, self.terms, self.vars)
            (kind, argkinds, freemap) = t
            local_termname = arg[1][0]

            termname = self.prefix + local_termname

            self.verify.add_term(termname, kind, argkinds, freemap)
            self.myterms[local_termname] = termname
            self.terms[local_termname] = termname
        elif cmd == 'stmt':
            # import context stmt command handling
            if len(arg) != 4:
                raise VerifyError('stmt needs exactly 4 arguments')
            (local_label, fv, local_hyps, local_stmt) = arg
            if type(local_label) != type('sym') or \
               type(fv) != type([]) or \
               type(local_hyps) != type([]):
                raise SyntaxError('Expected stmt (LABEL ((TVAR BVAR ...) ...) (HYP ...) CONCLUSION)')
            # Note that since we don't obtain stmt's from prior param
            # interfaces in the import context, we only have to check
            # the stmt label as prefixed for the verify context.
            label = self.prefix + local_label
            # out.write('label=', label, ' self.terms=', self.terms)
            varlist = []
            varmap = {}
            hyps = [self.map_syms(hyp, self.terms, varlist, varmap) for hyp in local_hyps]
            num_hypvars = len(varlist)
            stmt = self.map_syms(local_stmt, self.terms, varlist, varmap)
            for clause in fv:
                if type(clause) != type([]) or len(clause) < 2:
                    raise SyntaxError('Free variable contraint context clause must be a list of at least two variables')
                want = 'tvar'
                for vname in clause:
                    try:
                        v = self.vars[vname]
                    except KeyError:
                        raise VerifyError('Unknown variable in free variable constraint context: ' + vname)
                    except TypeError:
                        raise SyntaxError('Free variable constraint context clause items must be variables')
                    if v[0] != want:
                        raise VerifyError('In free variable constraint context clause, the first variable must be a term variable and the remaining variables must be binding variables')
                    want = 'var'
                    if vname not in varmap:
                        raise VerifyError('Variable %s in free variable constraint context does not occur in the hypotheses or conclusion of the statement %s' % (vname, local_label))

            self.verify.add_assertion('stmt', label, fv, hyps, stmt,
                                      varlist, num_hypvars, len(varlist),
                                      self.vars)
        elif cmd == 'param':
            self.param_cmd(arg)
        elif cmd == 'kindbind':
            # TODO. Note that the interface file kindbind command expects
            # two existing kinds and makes them equivalent.  This can occur
            # after earlier uses of the two separate kinds, and means that
            # kind comparisons throughout the verifier need to be
            # careful to recognize the equivalence.
            raise VerifyError("kindbind is not (yet at least) allowed in interfaces")
        else:
            out.write('*** Warning: unrecognized command ' + cmd + \
                  ' seen in import context. ***')

class ExportCtx(InterfaceCtx):
    def __init__(self, name, verify, prefix, params):
        InterfaceCtx.__init__(self, name, verify, prefix, params, 'export')
        self.assertions = {}

    def export_match(self, sexp, vexp, varmap, invmap, vsyms):
        """ Match export-context expression sexp against verify-context
            expression vexp, building variable map varmap from export-context
            variables to verify-context variables as one goes.
            Return True on success, or False on failure.
            Note that this applies both syntactical and proof checks.
        """
        if type(sexp) == type('var'):
            if type(vexp) != type('var'):
                return False
            vvar = varmap.get(sexp, None)
            if vvar is None:
                try:
                    v = self.vars[sexp]
                except KeyError:
                    return False
                # Check binding vs. term var and kinds
                vv = vsyms[vexp]
                binding_v = v[0]
                binding_vv = vv[0]
                if binding_v != binding_vv:
                    return False
                kind_v = v[1]
                kind_vv = vv[1]
                if not self.kinds_match(kind_v, kind_vv):
                    return False
                if vexp in invmap:
                    return False
                varmap[sexp] = vexp
                invmap[vexp] = sexp
                return True
            return vvar == vexp
        if type(vexp) != type([]):
            return False
        n = len(sexp)
        if n != len(vexp):
            return False
        tname = sexp[0]
        if type(tname) != type('var'):
            return False
        if not tname in self.terms:  # can't use a term we don't know yet
            return False
        prefname = self.prefix + tname
        if prefname != vexp[0]:
            return False
        n = n - 1
        for i in xrange(n):
            if not self.export_match(sexp[i + 1], vexp[i + 1], varmap, invmap, vsyms):
                return False
        return True

    def kinds_match(self, export_kind, verify_kind):
        # I suspect we also should follow self.verify.kinds in the other direction,
        # but would like a test case before putting it in.
        return (export_kind == verify_kind or 
            verify_kind == self.verify.kinds.get(export_kind))

    def do_cmd(self, cmd, arg, out):
        """ ExportCtx command processing """
        if cmd == 'kind':
            kprefixed = self.kind_cmd_common(arg)
            try:
                k = self.verify.kinds[kprefixed]
            except KeyError:
                raise VerifyError('The kind ' + kprefixed +
                                  ' does not occur in the verify context.')

        elif cmd in ('var', 'tvar'):
            self.var_cmd(cmd, arg)

        elif cmd == 'term':
            if type(arg) != type([]) or len(arg) < 2:
                raise SyntaxError("Expected 'term (KIND (TERMNAME VAR ...) (BVAR FVAR ...) ...)'")

            t = term_common(arg[0], arg[1], arg[2:],
                            self.kinds, self.terms, self.vars)
            (kind, argkinds, freemap) = t
            local_termname = arg[1][0]

            termname = self.prefix + local_termname

            try:
                (tkind, targkinds, tfreemap) = self.verify.terms[termname]
            except KeyError:
                raise VerifyError('The term symbol ' + termname +
                                  ' does not exist in the verify context.')

            # Check that the term from the verify context agrees with that
            # declared in the export context.
            if not self.kinds_match(kind, tkind):
                raise VerifyError('Term ' + local_termname +
                                  ' kind mismatch with verify context term ' +
                                  termname +
                                  '; exporting to kind ' + kind +
                                  ' but is ' + tkind + ' in verify context')

            if (len(argkinds) != len(targkinds)):
                raise VerifyError(\
                    'Term signature mismatch with verify context for ' + local_termname +
                    '; kinds being exported to: ' + str(argkinds) +
                    '; kinds in verify context: ' + str(targkinds))

            for i in range(len(argkinds)):
                if not self.kinds_match(argkinds[i], targkinds[i]):
                    raise VerifyError(\
                        'Term signature mismatch with verify context for ' + local_termname +
                        '; kinds being exported to: ' + str(argkinds) +
                        '; kinds in verify context: ' + str(targkinds))

            if freemap != tfreemap:
                raise VerifyError(\
                    'Term freemap mismatch with verify context for ' +
                    local_termname)
            
            self.myterms[local_termname] = termname
            self.terms[local_termname] = termname

        elif cmd == 'stmt':
            # Export context stmt command handling
            if len(arg) != 4:
                raise VerifyError('stmt needs exactly 4 arguments')
            (local_label, fv, local_hyps, local_conc) = arg
            if type(local_label) != type('sym') or \
               type(fv) != type([]) or \
               type(local_hyps) != type([]):
                raise SyntaxError('Expected stmt (LABEL ((TVAR BVAR ...) ...) (HYP ...) CONCLUSION)')
            # Note that since we don't obtain stmt's from prior param
            # interfaces in the export context, we only have to check
            # the stmt label as prefixed for the verify context.
            label = self.prefix + local_label
            try:
                (vkw, vfv, vhyps, vconcl, vmand, vsyms) = self.verify.syms[label]
            except KeyError:
                raise VerifyError('No symbol %s is known in verify context.' % label)
            except ValueError:
                raise VerifyError('The symbol %s is not an assertion in verify context' % label)

            if local_label in self.assertions:
                raise VerifyError('A statement with name %s already exists in export context.' % local_label)
            if local_label in self.vars:
                raise VerifyError('%s already exists as a variable in export context.' % local_label)


            # Check that the hypotheses and conclusion provided in export
            # context match those in verify context, apart from variable
            # renames (and term prefixing, of course)
            nhyps = len(local_hyps)
            if nhyps != len(vhyps):
                raise VerifyError('Different numbers of hypotheses between verify and export context for stmt %s' % local_label)

            varmap = {}
            invmap = {}
            for i in range(nhyps):
                hyp = local_hyps[i]
                vhyp = vhyps[i]
                if not self.export_match(hyp, vhyp, varmap, invmap, vsyms):
                    raise VerifyError('Hypothesis mismatch for stmt %s\nExport context:\n   %s\nVerify context:\n   %s' % (local_label, sexp_to_string(hyp), sexp_to_string(vhyp)))
            if not self.export_match(local_conc, vconcl, varmap, invmap, vsyms):
                raise VerifyError('Conclusion mismatch for stmt %s\nExport context:\n   %s\nVerify context:\n   %s' % (local_label, sexp_to_string(local_conc), sexp_to_string(vconcl)))

            # Would it make sense to save a 'nonfree' dictionary
            # with each stmt / thm added to the verify context?
            # For now, we reconstruct the nonfrees map here.
            nonfrees_orig = {}
            for clause in vfv:
                tvar = clause[0]
                for bvar in clause[1:]:
                    try:
                        d = nonfrees_orig[bvar]
                    except KeyError:
                        d = {}
                        nonfrees_orig[bvar] = d
                    d[tvar] = 0

            nonfrees = {}
            for clause in fv:
                if type(clause) != type([]) or len(clause) < 2:
                    raise SyntaxError('Free variable contraint context clause must be a list of at least two variables')
                want = 'tvar'
                for vname in clause:
                    try:
                        v = self.vars[vname]
                    except KeyError:
                        raise VerifyError('Unknown variable in free variable constraint context: ' + vname)
                    except TypeError:
                        raise SyntaxError('Free variable constraint context clause items must be variables')
                    if v[0] != want:
                        raise VerifyError('In free variable constraint context clause, the first variable must be a term variable and the remaining variables must be binding variables')
                    try:
                        vvar = varmap[vname]
                    except KeyError:
                        raise VerifyError('Variable %s in free variable constraint context does not occur in the hypotheses or conclusion of the statement %s' % (vname, local_label))
                    if want == 'tvar':
                        tvar = vvar
                    else:
                        # Hmm, we could perhaps allow stronger freeness
                        # constraints in the exported stmt than in the
                        # original, but for now we don't.
                        if not vvar in nonfrees_orig:
                            # not sure what this means, but at least give a line number
                            # by making it a VerifyError.
                            raise VerifyError('variable ' + vvar + ' not found in nonfrees ' + str(nonfrees_orig))
                        if not tvar in nonfrees_orig[vvar]:
                            raise VerifyError('Export context free variable constraint context for %s is too strong' % vname)
                        # Add tvar to the set of term variables in which vvar
                        # may not occur free.
                        d = nonfrees.get(vvar, None)
                        if d is None:
                            d = {}
                            nonfrees[vvar] = d
                        d[tvar] = 0
                    want = 'var'
            # Check that the (non)freeness constraints provided in the export
            # context are at least as strong as those in the verify context

            for vvar, d_orig in nonfrees_orig.iteritems():
                try:
                    d = nonfrees[vvar]
                except KeyError:
                    raise VerifyError('Export context free variable constraint context in stmt %d is too weak' % local_label)
                for v in d_orig:
                    if not v in d:
                        raise VerifyError('Export context free variable constraint context in stmt %d is too weak' % local_label)
                
            # Remember we've used a stmt with name local_label
            self.assertions[local_label] = 0
        elif cmd == 'param':
            self.param_cmd(arg)
        elif cmd == 'kindbind':
            # TODO. Note that the interface file kindbind command expects
            # two existing kinds and makes them equivalent.  This can occur
            # after earlier uses of the two separate kinds, and means that
            # kind comparisons throughout the verifier need to be
            # careful to recognize the equivalence.
            raise VerifyError("kindbind is not (yet at least) allowed in interfaces")
        else:
            out.write('*** Warning: unrecognized command ' + cmd + \
                  ' seen in export context. ***\n')

def run(urlctx, url, ctx, out):
    s = Scanner(urlctx.resolve(url))
    try:
        while 1:
            cmd = read_sexp(s)
            if cmd is None:
                return True
            if type(cmd) != str:
                raise SyntaxError('cmd must be atom: %s has type %s' % (cmd, type(cmd)))
            arg = read_sexp(s)
            ctx.do_cmd(cmd, arg, out)
    except VerifyError, x:
        out.write('Verify error at %s:%d:\n%s' % (url, s.lineno, x.why) + '\n')
        if ctx.error_handler is not None:
            ctx.error_handler('', x.why)
    except SyntaxError, x:
        out.write('Syntax error at line %s:%d:\n%s' % (url, s.lineno, str(x)) + '\n')
        if ctx.error_handler is not None:
            ctx.error_handler('', str(x))
    return False

if __name__ == '__main__':
    i = 1
    fail_continue = False
    class ErrorCounter:
        def __init__(self):
            self.count = 0
        def error_handler(self, label, msg):
            self.count += 1
            return fail_continue
    error_counter = ErrorCounter()
    while i < len(sys.argv):
        arg = sys.argv[i]
        if arg[0] != '-':
            break
        if arg == '--':
            i = i + 1
            break
        if arg == '-c':
            fail_continue = True
        else:
            print >> sys.stderr, 'Unknown option:', arg
        i = i + 1
        
    fn = sys.argv[i]
    urlctx = UrlCtx('', fn, sys.stdin)
    ctx = VerifyCtx(urlctx, run, error_counter.error_handler)
    if fn == '-':
        url = fn
    else :
        url = 'file://' + fn        
    ctx.run(urlctx, url, ctx, sys.stdout)
    if error_counter.count != 0:
        print 'Number of errors: %d' % error_counter.count
        sys.exit(1)

