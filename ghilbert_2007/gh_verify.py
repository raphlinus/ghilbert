#!/usr/bin/env python

# A prototype verifier for a Ghilbert variant with interfaces

import sys, string, array

verbosity = 1

# sexp_to_string is for printing of verify errors only
loose = 0

def sexp_to_string(sexp):
    buf = array.array('c')
    sexp_to_string_rec(buf, sexp)
    return buf.tostring()
def sexp_to_string_rec(buf, sexp):
    if type(sexp) == type('str'):
        buf.fromstring(sexp)
    elif type(sexp) == type([]):
        buf.fromstring('(')
        if loose:
            sp_string = ' '
        else:
            sp_string = ''
        for el in sexp:
            buf.fromstring(sp_string)
            sexp_to_string_rec(buf, el)
            sp_string = ' '
        if loose:
            buf.fromstring(' ')
        buf.fromstring(')')

class VerifyError(Exception):
    def __init__(self, why, label = None, stack = None):
        self.args = why
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

# Resolve an interface name into a Scanner object. This is simple now but
# may become more interesting.
def resolve_interface(interface_name):
    return Scanner(file(interface_name + '.ghi'))

# Apply map to (constant) symbols in a term
def map_syms(sexp, map):
    if type(sexp) == type('var'):
        return sexp
    elif type(sexp) == type([]):
        return [map[sexp[0]]] + [map_syms(el, map) for el in sexp[1:]]

# Convert dv list to canonical form (x, y pairs with x < y).
def canonize_dv(dv):
    result = []
    for el in dv:
        for i in range(len(el) - 1):
            for j in range(i + 1, len(el)):
                x, y = el[i], el[j]
                if x > y:
                    x, y = y, x
                if x != y and not (x, y) in result:
                    result.append((x, y))
    return result

class ProofCtx:
    def __init__(self):
        self.stack = []
        self.mandstack = []
        self.dv_needs = []

class VerifyGh:
    def __init__(self):
        self.kinds = {}
	self.terms = {}
        self.syms = {}
        self.interfaces = {}
    def do_cmd(self, cmd, arg):
        if verbosity >= 8: print cmd, sexp_to_string(arg)
        if cmd == 'var':
            kind = arg[0]
            if not self.kinds.has_key(kind):
                raise VerifyError('kind not known: ' + kind)
            for v in arg[1:]:
                if self.syms.has_key(v):
                    raise VerifyError('symbol already defined: ' + v)
                self.syms[v] = ('var', self.kinds[kind])
        elif cmd == 'def':
            (lhs, rhs) = arg
            label = lhs[0]
            if self.terms.has_key(label):
                raise VerifyError('term already defined: ' + label)
            args = lhs[1:]
            type = self.kindof_exp(rhs)
            types = map(self.kindof_exp, args)
            self.terms[label] = ('def', type, types, args, rhs)
        elif cmd == 'thm':
            (label, dv, hyps, stat, proof) = arg
            if verbosity >= 1: print 'verifying', label
            self.check_proof(label, dv, hyps, stat, proof)
            self.add_assertion('thm', label, dv, map(lambda x: x[1], hyps), stat, self.syms)
        elif cmd == 'import':
            (id, name, params, pref) = arg
            if pref[0] == '"' and pref[-1] == '"':
                pref = pref[1:-1]
            intf_sc = resolve_interface(name)
            if self.interfaces.has_key(id):
                raise VerifyError('interface already imported: ' + id)
            iparams = [self.interfaces[i] for i in params]
            intf = self.read_interface(intf_sc, iparams, pref)
            self.interfaces[id] = intf
        elif cmd == 'export':
            (id, name, params, pref) = arg
            if pref[0] == '"' and pref[-1] == '"':
                pref = pref[1:-1]
            intf_sc = resolve_interface(name)
            if self.interfaces.has_key(id):
                raise VerifyError('interface already in namespace: ' + id)
            iparams = [self.interfaces[i] for i in params]
            intf = self.export_interface(intf_sc, iparams, pref)
            self.interfaces[id] = intf
        elif cmd == 'kindbind':
            (old_k, new_k) = arg
            if not self.kinds.has_key(old_k):
                raise VerifyError('kind not known: ' + old_k)
            if self.kinds.has_key(new_k):
                raise VerifyError('kind already defined: ' + new_k)
            self.kinds[new_k] = self.kinds[old_k]
        else:
            print 'Unknown cmd: ' + cmd

    def kindof_exp(self, exp, syms = None):
        if type(exp) == type('var'):
            if syms == None:
                v = self.syms[exp]
            else:
                v = syms[exp]
            if v[0] != 'var':
                raise VerifyError('expression not a var: ' + exp)
            return self.kinds[v[1]]
        elif type(exp) == type([]):
            v = self.terms[exp[0]]
            if v[0] not in ('term', 'def'):
		# this won't happen, now that terms are in a separate namespace
                raise VerifyError('expression not a term: ' + exp[0])
            if len(exp) - 1 != len(v[2]):
                raise VerifyError('arity mismatch: ' + exp[0] + ' has arity ' + `len(v[2])` + ' but was given ' + `len(exp) - 1`)
            for i in range(len(exp) - 1):
                child_kind = self.kindof_exp(exp[i + 1], syms)
                if child_kind != self.kinds[v[2][i]]:
                    #print self.kinds
                    raise VerifyError('kind mismatch: ' + sexp_to_string(exp) + ' wanted ' + self.kinds[v[2][i]] + ' got ' + child_kind)
            return self.kinds[v[1]]

    def read_interface(self, sc, params, pref):
        kind_map = {}
        kind_map_new = {}
        sym_map = {} # should be term_map
        new_syms = [] # should be new_terms
        local_syms = {}
        param_ix = 0
        while 1:
            cmd = sc.get_tok()
            if cmd == None:
                break
            else:
                arg = read_sexp(sc)
                if verbosity > 10:
                    print 'interface cmd:', (cmd, arg)
                if cmd == 'kind':
                    local_k = arg[0]
                    k = pref + local_k
                    if self.kinds.has_key(k):
                        raise VerifyError('kind already defined: ' + k)
                    kind_map[local_k] = k
                    kind_map_new[local_k] = k
                    self.kinds[k] = k
                if cmd == 'kindbind':
                    (local_k_old, local_k_new) = arg
		    k_old = pref + local_k_old
                    k_new = pref + local_k_new
                    if not kind_map.has_key(local_k_old):
                        raise VerifyError('kind not known: ' + k_old)
                    if not kind_map.has_key(local_k_new):
                        raise VerifyError('kind not known: ' + k_new)
                    k = self.kinds[k_old]
                    # Note: the next three statements are mutations. The
                    # goal is to unify k_old and k_new in the kind maps.
                    kind_map[local_k_new] = k
                    kind_map_new[local_k_new] = k
                    self.kinds[k_new] = k
                elif cmd == 'var':
                    kind = arg[0]
                    if not kind_map.has_key(kind):
                        raise VerifyError('kind not known: ' + kind)
                    for v in arg[1:]:
                        if local_syms.has_key(v):
                            raise VerifyError('symbol already defined: ' + v)
                        local_syms[v] = ('var', kind_map[kind])
                elif cmd == 'term':
                    local_kind = arg[0]
                    kind = kind_map[local_kind]
                    for k in arg[1:]:
                        local_c = k[0]
                        c = pref + local_c
                        if self.terms.has_key(c):
                            raise VerifyError('term already defined: ' + c)
                        # todo: check that args are kinds
                        sym_map[local_c] = c
                        new_syms.append(local_c)
                        ks = [kind_map[el] for el in k[1:]]
                        self.terms[c] = ('term', kind, ks)
                elif cmd == 'stmt':
                    (local_label, dv, local_hyps, local_stat) = arg
                    label = pref + local_label
                    stat = map_syms(local_stat, sym_map)
                    hyps = [map_syms(hyp, sym_map) for hyp in local_hyps]
                    self.kindof_exp(stat, local_syms)
                    self.add_assertion('ax', label, dv, hyps, stat, local_syms)
                elif cmd == 'param':
                    (id, name, iparams, ipref) = arg
                    if ipref[0] == '"' and ipref[-1] == '"':
                        ipref = ipref[1:-1]
                    # todo: check iparams
                    (tag, ppref, kinds, syms) = params[param_ix]
                    param_ix += 1
                    assert(tag == 'intf')
                    for pk, k in kinds.iteritems():
                        local_k = ipref + pk
                        if kind_map.has_key(local_k):
                            raise VerifyError('kind already defined: ', local_k)
                        kind_map[local_k] = k
                    for ps in syms:
                        local_s = ipref + ps
                        s = ppref + ps
                        if sym_map.has_key(local_s):
                            raise VerifyError('symbol already defined: ', local_s)
                        sym_map[local_s] = s
        return ('intf', pref, kind_map_new, new_syms)

    # There's quite a bit of duplication between this and read_interface;
    # perhaps the two should be unified.
    def export_interface(self, sc, params, pref):
        kind_map = {}
        kind_map_new = {}
        sym_map = {}
        new_syms = []
        local_syms = {}
        param_ix = 0
        while 1:
            cmd = sc.get_tok()
            if cmd == None:
                break
            else:
                arg = read_sexp(sc)
                if verbosity > 10:
                    print 'exported interface cmd:', (cmd, arg)
                if cmd == 'kind':
                    local_k = arg[0]
                    k = pref + local_k
                    if not self.kinds.has_key(k):
                        raise VerifyError('exported kind not defined: ' + k)
                    kind_map[local_k] = self.kinds[k]
                    kind_map_new[local_k] = self.kinds[k]
                if cmd == 'kindbind':
                    (local_k_old, local_k_new) = arg
		    k_old = pref + local_k_old
                    k_new = pref + local_k_new
                    if not kind_map.has_key(local_k_old):
                        raise VerifyError('kind not known: ' + k_old)
                    if not kind_map.has_key(local_k_new):
                        raise VerifyError('kind not known: ' + k_new)
		    if self.kinds[k_old] != self.kinds[k_new]:
			raise VerifyError('exported kindbind not compatible: ' + k_old + ', ' + k_new)
                elif cmd == 'var':
                    kind = arg[0]
                    if not kind_map.has_key(kind):
                        raise VerifyError('kind not known: ' + kind)
                    for v in arg[1:]:
                        if local_syms.has_key(v):
                            raise VerifyError('symbol already defined: ' + v)
                        local_syms[v] = ('var', kind_map[kind])
                elif cmd == 'term':
                    local_kind = arg[0]
                    kind = self.kinds[kind_map[local_kind]]
                    for k in arg[1:]:
                        local_c = k[0]
                        c = pref + local_c
                        if not self.terms.has_key(c):
                            raise VerifyError('exported term not defined: ' + c)
			term = self.terms[c]
                        # todo: check that args are kinds
			if term[0] not in ('term', 'def'):
			    raise VerifyError('symbol ' + c + ' defined as ' + self.syms[c][0] + ' but attempted to export as term')
			c_kind, c_ks = term[1], term[2]
			if c_kind != kind:
			    raise VerifyError('term ' + c + ' defined with kind ' + c_kind + ' but attempted to export with kind ' + kind)
                        sym_map[local_c] = c
                        new_syms.append(local_c)
                        ks = [self.kinds[kind_map[el]] for el in k[1:]]
			if c_ks != ks:
			    print c_ks, ks
			    raise VerifyError('term ' + c + ' defined with args of kinds ' + ', '.join(c_ks) + ' but attempted to export with args of kinds ' + ', '.join(ks))
                elif cmd == 'stmt':
                    (local_label, dv, local_hyps, local_stat) = arg
                    label = pref + local_label
                    stat = map_syms(local_stat, sym_map)
                    hyps = [map_syms(hyp, sym_map) for hyp in local_hyps]
                    self.verify_assertion('ax', label, dv, hyps, stat, local_syms)
                elif cmd == 'param':
                    (id, name, iparams, ipref) = arg
                    if ipref[0] == '"' and ipref[-1] == '"':
                        ipref = ipref[1:-1]
                    # todo: check iparams
                    (tag, ppref, kinds, syms) = params[param_ix]
                    param_ix += 1
                    assert(tag == 'intf')
                    for pk, k in kinds.iteritems():
                        local_k = ipref + pk
                        if kind_map.has_key(local_k):
                            raise VerifyError('kind already defined: ', local_k)
                        kind_map[local_k] = k
                    for ps in syms:
                        local_s = ipref + ps
                        s = ppref + ps
                        if sym_map.has_key(local_s):
                            raise VerifyError('symbol already defined: ', local_s)
                        sym_map[local_s] = s
        return ('intf', pref, kind_map_new, new_syms)


    # match stat to target, expanding defs in stat as needed
    
    # forv is a list of variables (in target expression) that are forbidden
    # for use as definition dummies.

    # dvmap maps the used def dummy variables to the variables appearing in
    # the def; match_expand stores new dummies into this list

    def match_expand(self, stat, target, forv, dvmap, env = None, def_fv = None):
	#print 'match_expand', target, forv
        if type(stat) == type('var'):
            if env == None:
                return stat == target
            elif env.has_key(stat):
                return self.match_expand(env[stat], target, forv, dvmap)
            else:
                # bind dummy variable
                if type(target) != type('var'):
                    raise VerifyError('def dummy bound to non-var')
                if target in forv:
                    raise VerifyError('def dummy in hyp or concl: ' + target)
                if dvmap.has_key(target):
                    raise VerifyError('def dummy used twice: ' + target)
                dvmap[target] = def_fv
                env[stat] = target
                return 1
        elif type(stat) == type([]):
            if stat[0] == target[0]:
                if len(stat) != len(target):
                    raise VerifyError('Statement proved has arity mismatch')
                for i in range(1, len(stat)):
                    if not self.match_expand(stat[i], target[i], forv, dvmap, env, def_fv):
                        return 0
                return 1
            else:
                # def expansion
                defn = self.terms[stat[0]]
                if defn[0] != 'def':
                    raise VerifyError('expanding expected a defn: ' + stat[0])
                (kind, argkinds, args, expansion) = defn[1:]
                if verbosity >= 20:
                    print 'expand:', stat[0], kind, argkinds, args, expansion
                env = {}
                if len(args) != len(stat) - 1:
                    raise VerifyError('Def expansion has arity mismatch')
                def_fv = self.freevars(target)
                for i in range(len(args)):
                    env[args[i]] = stat[i + 1]
                return self.match_expand(expansion, target, forv, dvmap, env, def_fv)

    def check_proof_step(self, hypmap, step, proofctx):
        if type(step) == type([]):
            # must be a term
            kind = self.kindof_exp(step)
            proofctx.mandstack.append((kind, step))
        elif hypmap.has_key(step):
            if len(proofctx.mandstack) != 0:
                raise VerifyError('hyp expected 0 mand hyps, got %d' % len(proofctx.mandstack))
            proofctx.stack.append(hypmap[step])
        else:
            if not self.syms.has_key(step):
                raise VerifyError('unknown proof step: ' + step)
            v = self.syms[step]
            if v[0] == 'var':
                proofctx.mandstack.append((v[1], step))
            elif v[0] in ('ax', 'thm'):
                (dv, hyps, concl, mand) = v[1:]
                if len(mand) != len(proofctx.mandstack):
                    raise VerifyError('expected %d mand hyps, got %d' % (len(mand), len(proofctx.mandstack)))
                env = {}
                for i in range(len(mand)):
                    var, kind = mand[i]
                    el = proofctx.mandstack[i]
                    if el[0] != kind:
                        raise VerifyError('kind mismatch for ' + var + ': expected ' + kind + ' got ' + el[0])
                    self.match(var, el[1], env)
                sp = len(proofctx.stack) - len(hyps)
                savesp = sp
                if sp < 0:
                    raise VerifyError('stack underflow')
                for hyp in hyps:
                    el = proofctx.stack[sp]
                    self.match(hyp, el, env)
                    sp += 1
                for x, y in dv:
                    x_vars = self.freevars(env[x])
                    y_vars = self.freevars(env[y])
                    for gam in x_vars:
                        for delt in y_vars:
                            if gam == delt:
                                raise VerifyError("disjoint violation " + gam)
                            x, y = gam, delt
                            if x > y:
                                x, y = y, x
                            proofctx.dv_needs.append((x, y))
                result = self.apply_subst(concl, env)
                proofctx.stack[savesp:] = [result]
                proofctx.mandstack = []
                if verbosity == 9:
                    print step + ':', sexp_to_string(result)
                if verbosity == 8: print 'step: ' + sexp_to_string(step)
                if verbosity >= 10:
                    print sexp_to_string(step) + ':'
                    self.print_stack(proofctx.stack)

    def check_proof(self, label, stat_dv, hyps, stat, proof):
        if verbosity >= 10: print stat_dv, hyps, stat, proof
        hypmap = {}
        for hyp in hyps:
            hypmap[hyp[0]] = hyp[1]
        proofctx = ProofCtx()
        for step_ix in range(len(proof)):
            step = proof[step_ix]
            try:
                self.check_proof_step(hypmap, step, proofctx)
            except VerifyError, x:
                x.step = (step_ix, proof)
                x.stack = proofctx.stack
                x.label = label
                raise x
        canon_dv = canonize_dv(stat_dv)
	if len(proofctx.mandstack) != 0:
	    raise VerifyError('extra mand hyps on stack at end of proof', label)
        if len(proofctx.stack) != 1:
            raise VerifyError('stack must have one element at end of proof', label, proofctx.stack)
        forv = self.freevars(stat)
        for hyp in hyps:
            forv.extend(self.freevars(hyp))
        dvmap = {}
	#print 'forv =', forv, concl
        if not self.match_expand(stat, proofctx.stack[0], forv, dvmap):
            raise VerifyError('stack at end of proof is ' + sexp_to_string(proofctx.stack[0]) + ' wanted ' + sexp_to_string(stat), label)
	nondummies = self.freevars(proofctx.stack[0])
	for hyp in hyps:
	    nondummies.extend(self.freevars(hyp))
	for x, y in proofctx.dv_needs:
	    if x in nondummies and y in nondummies and not (x, y) in canon_dv:
		raise VerifyError("disjoint violation " + x + ", " + y)
        if dvmap != {}:
            for x, y in canon_dv:
                for u, v in (x, y), (y, x):
                    if dvmap.has_key(u):
                        if v in nondummies and not v in dvmap[u]:
                            raise VerifyError('def dummy ' + u + ' not distinct from ' + v)


    def print_stack(self, stack):
        for val in stack:
            print sexp_to_string(val)

    def print_step_context(self, step_ctx):
        width = 70
        step_ix, proof = step_ctx
        ctx = '{** ' + sexp_to_string(proof[step_ix]) + ' **}'
        left_ix = step_ix
        right_ix = step_ix + 1
        while left_ix > 0 or right_ix < len(proof):
            if left_ix > 0:
                left_ix -= 1
                try_ctx = sexp_to_string(proof[left_ix]) + ' ' + ctx
                if len(try_ctx) >= width:
                    break
                ctx = try_ctx
            if right_ix < len(proof):
                try_ctx = ctx + ' ' + sexp_to_string(proof[right_ix])
                if len(try_ctx) >= width:
                    break
                right_ix += 1
                ctx = try_ctx
        if left_ix > 0:
            ctx = '... ' + ctx
        if right_ix < len(proof):
            ctx = ctx + ' ...'
        print ctx

    def match(self, templ, exp, env):
        if type(templ) == type('var'):
            if env.has_key(templ):
                if exp != env[templ]:
                    print 'templ:', sexp_to_string(templ)
                    print 'exp:', sexp_to_string(exp)
                    print 'env:'
                    for (var, val) in env.items():
                        print ' ' + var + ':', sexp_to_string(val)
                    raise VerifyError('Unification error')
            else:
                env[templ] = exp
        elif type(templ) == type([]):
	    if type(exp) != type([]):
                raise VerifyError('Unification error, expected ' + sexp_to_string(templ) + ' got ' + exp)
            if templ[0] != exp[0]:
                raise VerifyError('Unification error, expected ' + templ[0] + ' got ' + exp[0])
            for i in range(1, len(templ)):
                self.match(templ[i], exp[i], env)

    # Apply a substitution
    def apply_subst(self, templ, env):
        if type(templ) == type('var'):
            return env[templ]
        elif type(templ) == type([]):
            return [templ[0]] + [self.apply_subst(el, env) for el in templ[1:]]

    def freevars(self, exp):
        fv = []
        self.freevars_rec(exp, fv)
        return fv
    def freevars_rec(self, exp, fv):
        if type(exp) == type('var'):
            if not exp in fv:
                fv.append(exp)
        elif type(exp) == type([]):
            for subexp in exp[1:]:
                self.freevars_rec(subexp, fv)

    def compute_mv(self, hyps, concl):
        mand = self.freevars(concl)
        for hyp in hyps:
            for var in self.freevars(hyp):
                if var in mand:
                    mand.remove(var)
        return mand

    def add_assertion(self, kw, label, dv, hyps, concl, syms):
        if self.syms.has_key(label):
            raise VerifyError('symbol already defined: ' + label)
        mand = self.compute_mv(hyps, concl)
        restrict_dv = []
        if len(dv):
            fv = self.freevars(concl)
            for hyp in hyps:
                fv.extend(self.freevars(hyp))
            for x, y in canonize_dv(dv):
                if x in fv and y in fv:
                    restrict_dv.append((x, y))
        mand2 = []
        for var in mand:
            if syms[var][0] != 'var':
                raise VerifyError('variable not defined: ' + var)
            mand2.append((var, syms[var][1]))
        self.syms[label] = (kw, restrict_dv, hyps, concl, mand2)

    def verify_assertion(self, kw, label, dv, hyps, concl, local_syms):
        if not self.syms.has_key(label):
            #raise VerifyError('exported symbol not defined: ' + label)
            print >> sys.stderr, 'exported symbol not defined: ' + label
            return
	if not self.syms[label][0] in ('thm', 'ax'):
	    raise VerifyError('exported symbol needs to be thm or stmt: ' + label)
	skw, sdv, shyps, sconcl, smand2 = self.syms[label]
	varmap = {}
	if len(hyps) != len(shyps):
	    raise VerifyError('number of hyps in exported symbol %s mismatch, have %d trying to export %d' % (label, len(shyps), len(hyps)))
	for i in range(len(hyps)):
	    if not self.match_export(shyps[i], hyps[i], varmap):
		raise VerifyError('hyp %s match fails in %s' % (label, i))
	if not self.match_export(sconcl, concl, varmap):
	    raise VerifyError('conclusion match fails in %s' % label)
	for k, v in varmap.items():
	    # check that every used variable has been defined
	    if not local_syms.has_key(v):
		raise VerifyError('variable %s not defined in %s' % (v, label))
	    elif not local_syms[v][0] == 'var':
		raise VerifyError('variable %s used, but is not a variable in %s' % (v, label))
	invmap = {}
	for k, v in varmap.items():
	    if invmap.has_key(v):
		raise VerifyError('var map not 1-1 in %s' % label)
	    invmap[v] = k
	cdv = canonize_dv(dv)
	for x, y in sdv:
	    xi = varmap[x]
	    yi = varmap[y]
	    if not ((xi, yi) in cdv or (yi, xi) in cdv):
		raise VerifyError('dv constraint %s,%s missing in export of %s' % (x, y, label))
	# Do we need to explicitly check mand hyps? I don't think so.

    def match_export(self, term, term_intf, varmap):
	if type(term) == type([]):
	    if type(term_intf) != type([]):
		return False
	    if term[0] != term_intf[0]:
		return False
	    for i in range(1, len(term)):
		if not self.match_export(term[i], term_intf[i], varmap):
		    return False
	    return True
	else:
	    if type(term_intf) == type([]):
		return False
	    if varmap.has_key(term):
		return varmap[term] == term_intf
	    else:
		varmap[term] = term_intf
		return True

def verify_gh(sc):
    vg = VerifyGh()
    while 1:
        cmd = sc.get_tok()
        if cmd == None:
            break
        else:
            try:
                arg = read_sexp(sc)
                vg.do_cmd(cmd, arg)
            except VerifyError, x:
                if x.label != None:
                    print 'Verification error at line', sc.lineno, 'in thm:', x.label
                else:
                    print 'Verification error at line', sc.lineno
                print x.args
                if x.step != None:
                    vg.print_step_context(x.step)
                if x.stack != None:
                    vg.print_stack(x.stack)
                return False
    if verbosity >= 100: print vg.syms
    return True

def verify_file(filename):
    sc = Scanner(file(filename))
    return verify_gh(sc)

if __name__ == '__main__':
    i = 1
    while i < len(sys.argv):
        arg = sys.argv[i]
        if len(arg) >= 2 and arg[:2] == '-v':
            if len(arg) > 2:
                param = arg[2:]
            else:
                i += 1
                param = sys.argv[i]
            verbosity = int(param)
        else:
            print >> sys.stderr, 'Unknown argument:', arg
        i += 1
    sc = Scanner(sys.stdin)
    allOK = verify_gh(sc)
    if not allOK:
    	sys.exit(1)
