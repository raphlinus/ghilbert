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
    def __init__(self, repobase, basefn):
	self.repobase = repobase
	self.base = os.path.split(basefn)[0]
    def resolve(self, url):
	# need to be careful about security if used on malicious inputs
	if url.startswith('file://'):
	    fn = url[7:]
	elif url.startswith('/'):
	    fn = os.path.join(self.repobase, url[1:])
	else:
	    fn = os.path.join(self.base, url)
	return file(fn)

class ProofCtx:
    def __init__(self, fvvarmap):
	self.stack = []
	self.mandstack = []
	self.fvvarmap = fvvarmap

class VerifyCtx:
    def __init__(self, urlctx, run):
	self.kinds = {}
	self.terms = {}
	self.syms = {}
	self.interfaces = {}
	self.urlctx = urlctx
	self.run = run
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
	self.terms[label] = (kind, argkinds, freemap)
    def add_assertion(self, kw, label, fv, hyps, concl, syms):
	mand = self.allvars(concl)
	for hyp in hyps:
	    for var in self.allvars(hyp):
		if var in mand:
		    mand.remove(var)
	#for var in mand:
	#    if not (syms.has_key(var) and syms[var][0] in ('var', 'tvar')):
	#	raise VerifyError('Variable not defined: ' + var)
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

    def free_in(self, var, term, fvvars):
	if type(term) == str:
	    tvar = self.syms[term]
	    if tvar[0] == 'var' or fvvars == None:
		return var == term
	    return not term in fvvars
	else:
	    freemap = self.terms[term[0]][2]
	    subterms = term[1:]
	    for v, m in freemap.items():
		if term[v + 1] == var:
		    subterms = [term[i + 1] for i in m]
	    for subterm in subterms:
		if self.free_in(var, subterm, fvvars):
		    return True
	    return False
    def kind_of(self, exp, syms = None):
	if type(exp) == type('var'):
	    if syms == None:
		v = self.syms[exp]
	    else:
		v = syms[exp]
	    if v[0] not in ('var', 'tvar'):
		raise VerifyError('expression not a var: ' + exp)
	    return self.kinds[v[1]]
	elif type(exp) == type([]):
	    if len(exp) == 0:
		raise VerifyError("term can't be empty list")
	    if type(exp[0]) != type('var'):
		raise VerifyError('term must be id, got ' + sexp_to_string(exp[0]))
	    if not self.terms.has_key(exp[0]):
		raise VerifyError('term ' + exp[0] + ' not known')
	    v = self.terms[exp[0]]
	    if len(exp) - 1 != len(v[1]):
		print exp, v
                raise VerifyError('arity mismatch: ' + exp[0] + ' has arity ' + `len(v[1])` + ' but was given ' + `len(exp) - 1`)
            for i in range(len(exp) - 1):
                child_kind = self.kind_of(exp[i + 1], syms)
                if child_kind != self.kinds[v[1][i]]:
                    #print self.kinds
                    raise VerifyError('kind mismatch: ' + sexp_to_string(exp) + ' wanted ' + self.kinds[v[1][i]] + ' got ' + child_kind)
            return self.kinds[v[0]]

    def do_cmd(self, cmd, arg):
	if cmd == 'import':
	    iname = arg[0]
	    url = arg[1]
	    params = arg[2]
	    prefix = arg[3]
	    if len(prefix) < 2 or prefix[0] != '"' or prefix[-1] != '"':
		raise SyntaxError('Namespace prefix must be enclosed in quotes')
	    prefix = prefix[1:-1]
	    importctx = ImportCtx(self, prefix)
	    self.run(self.urlctx, url, importctx)
	if cmd in ('var', 'tvar'):
	    kind = self.get_kind(arg[0])
	    for v in arg[1:]:
		self.add_sym(v, (cmd, kind))
	elif cmd == 'kindbind':
	    self.add_kind(arg[1], self.get_kind(arg[0]))
	elif cmd == 'thm':
	    if len(arg) < 5:
		raise VerifyError('Expected at least 5 args to thm')
	    (label, fv, hyps, stmt) = arg[:4]
	    print 'thm', label
	    proof = arg[4:]
	    # todo: add switch for lenient or no
	    try:
		self.check_proof(label, fv, hyps, stmt, proof)
	    except VerifyError, x:
		print 'error in thm ' + label + ': ' + x.why
	    self.add_assertion('thm', label, fv, hyps[1::2], stmt, self.syms)

    def check_proof(self, label, fv, hyps, stmt, proof):
	if len(hyps) & 1:
	    raise VerifyError('hyp list must be even')
	fvmap = {}
	for var in self.allvars(stmt):
	    if not var in self.syms:
		raise VerifyError('variable not found: ' + var)
	    if self.syms[var][0] == 'var':
		fvmap[var] = {}
	hypmap = {}
	for i in range(0, len(hyps), 2):
	    if type(hyps[i]) != type('label'):
		raise VerifyError('hyp label must be string')
	    hypmap[hyps[i]] = hyps[i + 1]
	    for var in self.allvars(hyps[i + 1]):
		if not var in self.syms:
		    raise VerifyError('variable not found: ' + var)
		if self.syms[var][0] == 'var':
		    fvmap[var] = {}
	    self.kind_of(hyps[i + 1])
	for clause in fv:
	    if type(clause) != type([]) or len(clause) == 0:
		raise VerifyError('each fv clause must be list of vars')
	    tvar = clause[0]
	    if type(tvar) != type('var'):
		raise VerifyError('var in fv clause must be string')
	    if not (self.syms.has_key(tvar) and self.syms[tvar][0] == 'tvar'):
		raise VerifyError('first var in fv clause must be tvar: ' + tvar)
	    for var in clause[1:]:
		if type(var) != type('var'):
		    raise VerifyError('var in fv clause must be string')
		if not (self.syms.has_key(var) and self.syms[var][0] == 'var'):
		    raise VerifyError('subsequent var in fv clause must be var: ' + var)
		if not fvmap.has_key(var):
		    raise VerifyError('spurious var in fv list: ' + var)
		fvmap[var][tvar] = 0
	#print 'hypmap =', hypmap
	#print 'fvmap =', fvmap
	proofctx = ProofCtx(fvmap)
	for step in proof:
	    #print 'step:', step
	    if step == '?':
		for x in proofctx.stack:
		    print sexp_to_string(x)
		continue
	    try:
		self.check_proof_step(hypmap, step, proofctx)
	    except VerifyError, x:
		x.why += ' [' + sexp_to_string(step) + ']'
		raise x
	if len(proofctx.mandstack) != 0:
	    raise VerifyError('extra mand hyps on stack at and of proof', label)
	if len(proofctx.stack) != 1:
	    raise VerifyError('stack must have one term at end of proof', label, proofctx.stack)
	if proofctx.stack[0] != stmt:
	    raise VerifyError('stack has ' + sexp_to_string(proofctx.stack[0]) + ' wanted ' + sexp_to_string(stmt), label)

    # These are really methods of both the verify and proofctx objects, and
    # are here by tradition.
    def check_proof_step(self, hypmap, step, proofctx):
	if type(step) == type([]):
	    kind = self.kind_of(step)
	    #print 'kind of ' + sexp_to_string(step) + ' = ' + kind
	    proofctx.mandstack.append((('tvar', kind), step))
	elif hypmap.has_key(step):
	    if len(proofctx.mandstack) != 0:
		raise VerifyError('hyp expected no mand hyps, got %d' % len(proofctx.mandstack))
	    proofctx.stack.append(hypmap[step])
	else:
	    if not self.syms.has_key(step):
		raise VerifyError('unknown proof step: ' + step)
	    v = self.syms[step]
	    if v[0] in ('var', 'tvar'):
		proofctx.mandstack.append((v, step))
	    elif v[0] in ('stmt', 'thm'):
		(fv, hyps, concl, mand, syms) = v[1:]
		if len(mand) != len(proofctx.mandstack):
                    raise VerifyError('expected %d mand hyps, got %d' % (len(mand), len(proofctx.mandstack)))
		env = {}
		for i in range(len(mand)):
		    var = mand[i]
		    tkind = syms[var]
		    el = proofctx.mandstack[i]
		    if el[0][1] != tkind[1]:
			raise VerifyError('kind mismatch for ' + var + ': expected ' + tkind[1] + ' got ' + el[0][1])
		    self.match(var, el[1], env)
		sp = len(proofctx.stack) - len(hyps)
		if sp < 0:
		    raise VerifyError('stack underflow')
		for i in range(len(hyps)):
		    el = proofctx.stack[sp + i]
		    self.match(hyps[i], el, env)
		for clause in fv:
		    tvar = clause[0]
		    for var in clause[1:]:
			if self.free_in_proof(env[var], env[tvar], proofctx):
			    raise VerifyError('expected ' + env[var] + ' not free in ' + sexp_to_string(env[tvar]))
		invmap = {}
		for var, exp in env.items():
		    if syms[var][0] == 'var':
			if type(exp) != type('var'):
			    raise VerifyError('expected binding variable for ' + var)
			if self.syms[exp][0] != 'var':
			    raise VerifyError('expected binding variable for ' + var + '; ' + exp + ' is term variable')
			if invmap.has_key(exp):
			    raise VerifyError('binding variables ' + invmap[exp] + ' and ' + var + ' both map to ' + exp)
			invmap[exp] = var
		#print 'env:', env, 'syms:', syms, 'invmap:', invmap
		result = self.apply_subst(concl, env)
		proofctx.stack[sp:] = [result]
		proofctx.mandstack = []
		#print 'stack:', proofctx.stack


    def free_in_proof(self, var, term, proofctx):
	return self.free_in(var, term, proofctx.fvvarmap.get(var, None))

    def match(self, templ, exp, env):
	if type(templ) == type('var'):
	    if env.has_key(templ):
		if exp != env[templ]:
		    # todo: more debug detail
		    raise VerifyError('Unification error')
	    else:
		env[templ] = exp
	elif type(templ) == type([]):
	    if type(exp) != type([]):
		raise VerifyError('Unification error, expected ' + sexp_to_string(templ) + ' got ' + exp)
	    if templ[0] != exp[0]:
		raise VerifyError('Unification error, expected ' + templ[0] + ' got ' + exp[0])
	    # todo: next check should never trigger, I think all terms
	    # given to match are well-formed.
	    if len(exp) != len(templ):
		raise VerifyError('Term ' + templ[0] + ' expects arity ' + `len(templ)` + ' got ' + `len(exp)`)
	    for i in range(1, len(templ)):
		self.match(templ[i], exp[i], env)

    def apply_subst(self, templ, env):
        if type(templ) == type('var'):
            return env[templ]
        elif type(templ) == type([]):
            return [templ[0]] + [self.apply_subst(el, env) for el in templ[1:]]

# Apply map to (constant) symbols in a term
def map_syms(sexp, map):
    if type(sexp) == type('var'):
        return sexp
    elif type(sexp) == type([]):
        return [map[sexp[0]]] + [map_syms(el, map) for el in sexp[1:]]

class ImportCtx:
    def __init__(self, verify, prefix):
	self.verify = verify
	self.prefix = prefix
	self.vars = {}
	self.term_map = {}
	#self.kinds = {}
    def get_kind(self, rawkind):
	return self.verify.get_kind(self.prefix + rawkind)
    def do_cmd(self, cmd, arg):
	if cmd == 'kind':
	    if type(arg) != type([]) or len(arg) != 1:
		raise VerifyError('kind takes one arg')
	    if type(arg[0]) != type('str'):
		raise VerifyError('kind must be string')
	    kind = self.prefix + arg[0]
	    self.verify.add_kind(kind, kind)
	elif cmd in ('var', 'tvar'):
	    kind = self.get_kind(arg[0])
	    for v in arg[1:]:
		if self.vars.has_key(v):
		    raise VerifyError('Variable ' + v + ' already defined')
		self.vars[v] = (cmd, kind)
	elif cmd == 'term':
	    kind = self.get_kind(arg[0])
	    local_termname = arg[1][0]
	    termname = self.prefix + local_termname
	    argkinds = []
	    freemap = {}
	    invmap = {}
	    args = arg[1][1:]
	    for i in range(len(args)):
		v = args[i]
		var = self.vars[v]
		if v in invmap:
		    raise VerifyError('Variable ' + v + ' not unique')
		invmap[v] = i
		argkinds.append(var[1])
		if var[0] == 'var':
		    freemap[i] = []
	    for freespec in arg[2:]:
		bv = invmap[freespec[0]]
		if not freemap.has_key(bv):
		    print freemap, bv
		    raise VerifyError('Binding variable ' + bv + ' not found')
		if freemap[bv] != []:
		    raise VerifyError('More than one freespec for ' + bv)
		freemap[bv] = [invmap[x] for x in freespec[1:]]
	    self.verify.add_term(termname, kind, argkinds, freemap)
	    self.term_map[local_termname] = termname
	elif cmd == 'stmt':
	    (local_label, fv, local_hyps, local_stmt) = arg
	    label = self.prefix + local_label
	    stmt = map_syms(local_stmt, self.term_map)
	    hyps = [map_syms(hyp, self.term_map) for hyp in local_hyps]
	    # TODO: verify kind consistency
	    self.verify.add_assertion('stmt', label, fv, hyps, stmt, self.vars)

def run(urlctx, url, ctx):
    s = Scanner(urlctx.resolve(url))
    try:
	while 1:
	    cmd = read_sexp(s)
	    if cmd is None:
		return True
	    if type(cmd) != str:
		raise SyntaxError('cmd must be atom')
	    arg = read_sexp(s)
	    ctx.do_cmd(cmd, arg)
    except VerifyError, x:
	print 'Verify error at %s:%d: %s' % (url, s.lineno, x.why)
    except SyntaxError, x:
	print 'Syntax error at line %s:%d: %s' % (url, s.lineno, str(x))
    return False

if __name__ == '__main__':
    fn = sys.argv[1]
    urlctx = UrlCtx('', fn)
    ctx = VerifyCtx(urlctx, run)
    url = 'file://' + fn
    ctx.run(urlctx, url, ctx)
