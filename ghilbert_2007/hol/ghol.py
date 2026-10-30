# Rough draft of HOL logic with Ghilbert proof output

import array

class VerifyError(Exception):
    def __init__(self, why):
        self.why = why
    def __str__(self):
        return self.why

def format_sexp_rec(sexp, buf):
    if type(sexp) == type('atom'):
        buf.fromstring(sexp)
    else:
        buf.fromstring('(')
        for i in range(len(sexp)):
            if i: buf.fromstring(' ')
            format_sexp_rec(sexp[i], buf)
        buf.fromstring(')')

def format_sexp(sexp):
    buf = array.array('c')
    format_sexp_rec(sexp, buf)
    return buf.tostring()

def flattenrec(result, list):
    if type(list) == type('string'):
        result.append(list)
    else:
        for el in list:
            flattenrec(result, el)
def flatten(list):
    result = []
    flattenrec(result, list)
    return result

class Type:
    def cmp(self, other):
        # placeholder
        return self.get_sexp() == other.get_sexp()

class bool_class(Type):
    def get_sexp(self):
        return ['bool']
    def prove_istype(self, tyenv):
        return 'boolistype'
    def __str__(self):
        return 'bool'

class ind_class(Type):
    def get_sexp(self):
        return ['$ind']
    def prove_istype(self, tyenv):
        return 'indistype'
    def __str__(self):
        return 'ind'

class fun_class(Type):
    def __init__(self, l, r):
        self.l = l
        self.r = r
    def get_sexp(self):
        return ['$->', self.l.get_sexp(), self.r.get_sexp()]
    def prove_istype(self, tyenv):
        return [self.l.prove_istype(tyenv), self.r.prove_istype(tyenc), 'arrowistype']
    def __str__(self):
        return '(' + str(self.l) + '->' + str(self.r) + ')'

def mk_type(name, args):
    if name == 'bool':
        return bool_class()
    if name == 'ind':
        return ind_class()
    elif name == 'fun':
        return fun_class(args[0], args[1])
    else:
        raise VerifyError('unknown mk_type name: ' + name)

class vartype_class(Type):
    def __init__(self, name):
	self.name = name
    def get_sexp(self):
	return self.name
    def prove_istype(self, tyenv):
	bound_ty, bound_env = tyenv[self.name]
	return bound_ty.prove_istype(bound_env)

def mk_vartype(name):
    return vartype_class(name)

# sugar to make hand-built types less painful
bool_type = mk_type('bool', [])
ind_type = mk_type('ind', [])
def arrow(l, r):
    return mk_type('fun', [l, r])

class Term:
    def __str__(self):
        return format_sexp(self.get_sexp())

class var_class(Term):
    def __init__(self, var, type):
        self.var = var
        self.type = type
    def get_sexp(self):
        return ['var', self.var, self.type.get_sexp()]
    def get_type(self):
        return self.type
    def prove_type(self, tyenv):
        return [self.type.prove_istype(tyenv), self.var, 'var:']
    def __str__(self):
        return self.var + ':' + str(self.type)

#
def mk_var(var, type):
    return var_class(var, type)

class eq_class(Term):
    def __init__(self, type):
	self.type = type
    def get_sexp(self):
	return ['$=', self.type.get_sexp()]
    def get_type(self):
	return arrow(self.type, arrow(self.type, bool_type))
    def prove_type(self, tyenv):
	return [self.type.prove_istype(tyenv), 'eq:']
    def __str__(self):
	return '$=' + str(self.type)

def mk_eq(x, y):
    return mk_comb(mk_comb(eq_class(x.get_type()), x), y)

def dest_eq_ty(t):
    if not isinstance(t, comb_class):
	raise VerifyError('not an equality: ' + str(t))
    if not isinstance(t.l, comb_class):
	raise VerifyError('not an equality: ' + str(t))
    if not isinstance(t.l.l, eq_class):
	raise VerifyError('not an equality: ' + str(t))
    return (t.l.r, t.r, t.l.l.type)

class imp(Term):
    def get_sexp(self):
        return ['$==>']
    def get_type(self):
        return arrow(bool_type, arrow(bool_type, bool_type))
    def prove_type(self, tyenv):
        return 'imptype'

class comb_class(Term):
    def __init__(self, l, r):
        self.l = l
        self.r = r
        lt = l.get_type()
        rt = r.get_type()
        if not isinstance(lt, fun_class):
            raise VerifyError('left term not a function')
        if not lt.l.cmp(rt):
            raise VerifyError("type of argument doesn't match")
    def get_type(self):
	lt = self.l.get_type()
	return lt.r
    def get_sexp(self):
        return ['.', self.l.get_sexp(), self.r.get_sexp()]
    def prove_type(self, tyenv):
        return [self.l.prove_type(tyenv), self.r.prove_type(tyenv), 'app:']
    def __str__(self):
        return '(' + str(self.l) + ' . ' + str(self.r) + ')'

def mk_comb(l, r):
    return comb_class(l, r)

class abs_class(Term):
    def __init__(self, v, ty, t):
        self.v = v
	self.ty = ty
        self.t = t
    def get_sexp(self):
        return ['lambda', self.v, self.ty.get_sexp(), self.t.get_sexp()]
    def get_type(self):
        return arrow(self.ty, self.t.get_type())
    def prove_type(self, tyenv):
        return [self.ty.prove_istype(tyenv), self.t.prove_type(tyenv), self.v, 'abs:']
    def __str__(self):
        return '\\' + self.v + ':' + str(self.ty) + '. ' + str(self.t)

def mk_abs(t1, t2):
    if not isinstance(t1, var_class):
        raise VerifyError("first arg of mk_abs must be a variable")
    return abs_class(t1.var, t1.type, t2)

def assums_to_sexp(assums):
    if assums == None:
        return ['true']
    elif isinstance(assums, Term):
        return assums.get_sexp()
    else:
        return ['$,', assums_to_sexp(assums[0]), assums_to_sexp(assums[1])]

class Thm:
    # assums is a binary tree
    def __init__(self, assums, concl):
	self.assums = assums
	self.concl = concl
    def get_sexp(self):
        return ['$|-', assums_to_sexp(self.assums), self.concl.get_sexp()]

class ASSUME(Thm):
    def __init__(self, t):
        # note: no checking here of t's bool-ness; if it doesn't hold,
        # the proof will fail to go through.
        self.assums = t
        self.concl = t
    def prove(self, tyenv):
        return [self.concl.prove_type(tyenv), 'ASSUME']

class REFL(Thm):
    def __init__(self, t):
	self.t = t
        self.assums = None
        self.concl = mk_eq(t, t)
    def prove(self, tyenv):
        return [self.t.prove_type(tyenv), 'REFL']

def BETA_term(v, ty, t1, t2):
    if isinstance(t1, var_class):
        if t1.var == v:
            return t2	
        else:
            return t1
    elif isinstance(t1, comb_class):
        tl = BETA_term(v, ty, t1.l, t2)
        tr = BETA_term(v, ty, t1.r, t2)
        return mk_comb(tl, tr)
    elif isinstance(t1, abs_class):
	if t1.v == v:
	    return t1
	# todo: check t1.v appears free in t2; alpha-conv
	t = BETA_term(v, ty, t1.t, t2)
	return mk_abs(mk_var(t1.v, t1.ty), t)

# Return value is proof of "(\v:ty . t1) t2 = redex" if v appears
# free in t1, else None
def BETA_proof(v, ty, t1, t2, tyenv):
    if isinstance(t1, var_class):
        if t1.var == v:
            return [t2.prove_type(tyenv), v, 'BETA1']
        else:
	    return None
    elif isinstance(t1, comb_class):
        pl = BETA_proof(v, ty, t1.l, t2, tyenv)
        pr = BETA_proof(v, ty, t1.r, t2, tyenv)
        if pl != None and pr != None:
            return [pl, pr, 'BETA3']
        elif pl != None:
            return [pl, t1.r.prove_type(tyenv), 'BETA31']
        elif pr != None:
            return [t1.l.prove_type(tyenv), pr, 'BETA32']
        else:
            return None
    elif isinstance(t1, abs_class):
       # todo: check t1.v == v; either separate case or alpha-conv
       # todo: check t1.v appears free in t2; alpha-conv
       pt = BETA_proof(v, ty, t1.t, t2, tyenv)
       if pt != None:
           return [pt, t1.ty.prove_istype(tyenv), t1.v, 'BETA4']
       else:
	   return None

class BETA_CONV(Thm):
    def __init__(self, t):
	if not isinstance(t, comb_class):
	    raise VerifyError('arg to BETA_CONV must be redex')
	if not isinstance(t.l, abs_class):
	    raise VerifyError('arg to BETA_CONV must be redex')
	self.v = t.l.v
	self.ty = t.l.ty
	self.t1 = t.l.t
	self.t2 = t.r
	self.assums = None
	print '#', self.v, self.ty, self.t1, self.t2
	self.concl = mk_eq(t, BETA_term(self.v, self.ty, self.t1, self.t2))
    def prove(self, tyenv):
	proof = BETA_proof(self.v, self.ty, self.t1, self.t2, tyenv)
	if proof == None:
	    proof = [t2.prove_type(tyenv), t1.prove_type(tyenv), v, 'BETA2']
	return proof

class ABS(Thm):
    def __init__(self, v, t):
	self.assums = t.assums
	self.v = v
	self.t = t
	x, y, ty = dest_eq_ty(t.concl)
	self.concl = mk_eq(mk_abs(v, x), mk_abs(v, y))
    def prove(self, tyenv):
	return [self.v.get_type().prove_istype(tyenv),
		self.t.prove(tyenv), self.v.var, 'ABS']

def print_gh_prolog():
    print 'import (HOL hol/hol () "")'
#    print 'import (HOL-DERIVED hol/hol-derived (HOL) "")'

    print 'var (var x y z)'

def print_thm_gh(thm, name, tyenv = {}):
    print 'thm (' + name
    print '  () # dv\'s'
    print '  () # hyps'
    print '  ' + format_sexp(thm.get_sexp())
    print '  ' + format_sexp(flatten(thm.prove(tyenv)))
    print ')'

def random_junk():
    x = mk_var('x', ind_type)
    ind_ind = mk_type('fun', [ind_type, ind_type])
    y = mk_var('y', ind_ind)
    z = mk_var('z', ind_ind)
    t = mk_comb(mk_abs(y, z), mk_abs(x, x))
    print_thm_gh(REFL(t), 'foo')
    print str(BETA_CONV(t))

def test2():
    x = mk_var('x', ind_type)
    y = mk_var('y', ind_type)
    z = mk_var('z', ind_type)
    thm1 = ASSUME(mk_eq(x, y))
    thm2 = ABS(z, thm1)
    print_thm_gh(thm2, 'test2')

if __name__ == '__main__':
    print_gh_prolog()
    x = mk_var('x', ind_type)
    y = mk_var('y', ind_type)
    print_thm_gh(BETA_CONV(mk_comb(mk_abs(x, x), y)), 'foo')
    test2()
