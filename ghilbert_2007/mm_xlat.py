#!/usr/bin/env python

import re
import string
import array

# The following commands may be useful to split the stdout of this
# script to Ghilbert interface and proof files, respectively:
#
# grep -v -E '^thm' ../raw.gh > set_mm.ghi
# grep -E '^(thm|var)' ../raw.gh > set_mm.gh
#
# They'll need a bit of manual fixup:
# 1. The gh needs to import the ghi

verbosity = 0
loose = 0

# The term_renames are because parens are not valid as part
# of a token. Currently, thm_renames are doubly not required, because
# both Ghilbert has separate names for terms and proof steps, and
# because the new policy of set.mm is to enforce such separation
# anyway.

thm_rename = {}
term_rename = {'(.': 'C:', '(_': 'C_', '(/)': '{/}',
	       '(,)': '],[', '(,]': '],]', '[,)': '[,['}

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

class toks:
    def __init__(self, lines):
        self.lines = lines
	self.line = None
	self.pos = 0
	self.tok_re = re.compile(r'\s*(\$[\(\)]|\S+)')
    def read(self, re = None):
        while 1:
	    if self.line == None:
		self.line = self.lines.readline()
		if self.line == '':
		    return None
		self.pos = 0
	    tok_m = self.tok_re.match(self.line, self.pos)
	    if tok_m:
		self.pos = tok_m.end()
		return tok_m.group(1)
	    else:
		self.line = None
    def read_comment(self):
	if self.line == None:
	    self.line = self.lines.readline()
	    if self.line == '':
		return None
	    self.pos = 0
	pos = self.line.find('$)', self.pos)
	if pos == self.pos:
	    self.pos = pos + 2
	    result = '$)'
	elif pos >= 0:
	    result = self.line[self.pos:pos]
	    self.pos = pos
	else:
	    result = self.line[self.pos:].rstrip()
	    self.line = None
	return result

class Frame:
    def __init__(self):
        self.c = []
        self.v = []
        self.d = []
        self.f = []
        self.e = []
        self.elabels = []

class FrameStack:
    def __init__(self):
        self.stack = []
    def push(self):
        frame = Frame()
        self.stack.append(frame)
    def pop(self):
        self.stack.pop()
    def add_c(self, tok):
        frame = self.stack[-1]
        if tok in frame.c:
            raise 'const already defined in scope'
        frame.c.append(tok)
        if tok in frame.v:
            raise 'const already defined as var in scope'
        frame.c.append(tok)
    def add_v(self, tok):
        frame = self.stack[-1]
        if tok in frame.v:
            raise 'var already defined in scope'
        if tok in frame.c:
            raise 'var already defined as const in scope'
        frame.v.append(tok)
    def add_f(self, var, kind):
        if not self.lookup_v(var):
            raise ('var in $f not defined: ' + var)
        if not self.lookup_c(kind):
            raise ('const in $f not defined' + kind)
        frame = self.stack[-1]
        for (v, k) in frame.f:
            if v == var:
                raise 'var in $f already defined in scope'
        frame.f.append((var, kind))
    def add_e(self, label, stat):
        frame = self.stack[-1]
        frame.e.append(stat)
        frame.elabels.append(label)
    def add_d(self, stat):
        frame = self.stack[-1]
        for i in range(len(stat)):
            for j in range(i + 1, len(stat)):
                x, y = stat[i], stat[j]
                if x > y:
                    x, y = y, x
                if x != y and not (x, y) in frame.d:
                    frame.d.append((x, y))
    def lookup_c(self, tok):
        for i in range(len(self.stack) - 1, -1, -1):
            if tok in self.stack[i].c:
                return 1
    def lookup_v(self, tok):
        for i in range(len(self.stack) - 1, -1, -1):
            if tok in self.stack[i].v:
                return 1
    def lookup_f(self, var):
        for i in range(len(self.stack) - 1, -1, -1):
            frame = self.stack[i]
            for (v, k) in frame.f:
                if v == var:
                    return k
    def lookup_d(self, x, y):
        # return 1 if disjoint, None if not
        if x > y:
            x, y = y, x
        for i in range(len(self.stack) - 1, -1, -1):
            frame = self.stack[i]
            if (x, y) in frame.d:
                return 1
    def get_dv(self, fv):
        dv = []
        for i in range(len(self.stack) - 1, -1, -1):
            frame = self.stack[i]
            for d in frame.d:
                gh_dv = []
                for v in d:
                    if v in fv:
                        gh_dv.append(v)
                if len(gh_dv) >= 2:
                    dv.append(gh_dv)
        return dv
    def make_assertion(self, stat):
        mand_vars = []
        hyps = []
        for fr in self.stack:
            hyps.extend(fr.e)
        frame = self.stack[-1]
        visible = hyps[:]
        visible.append(stat)
        for hyp in visible:
            for tok in hyp:
                if self.lookup_v(tok) and tok not in mand_vars:
                    mand_vars.append(tok)
        dm = []
        for i in range(len(self.stack)):
            fr = self.stack[i]
            for (x, y) in fr.d:
                if x in mand_vars and y in mand_vars and not (x, y) in dm:
                    dm.append((x, y))
        mand_hyps = []
        for i in range(len(self.stack) - 1, -1, -1):
            fr = self.stack[i]
            for j in range(len(fr.f) - 1, -1, -1):
                (v, k) = fr.f[j]
                if v in mand_vars:
                    mand_hyps.append((k, v))
                    mand_vars.remove(v)
        mand_hyps.reverse()
        if verbosity >= 18:
            print 'ma:', (dm, mand_hyps, hyps, stat)
        return (dm, mand_hyps, hyps, stat)

class MM:
    c_conn = ('=', 'e.', '=/=', 'e/', '(_', '(.', 'Po', 'Or', 'Fr', 'We', 'Fn')
    c_bin = ('\\', 'u.', 'i^i', 'X.', '|`', '"', 'o.', '`', '/.')
    c_un = ('P~', 'suc', "`'", 'dom', 'ran', '-u')
    c_pred = ('Tr', 'Ord', 'Lim', 'Rel', 'Fun', 'Er')

    labelmap = {'weq': 'wceq', 'wel': 'wcel', 'wsb': 'wsbc'}

    def __init__(self):
        self.fs = FrameStack()
        self.labels = {}
        self.n_mm_steps = 0
        self.n_gh_steps = 0
        self.seenvar = {}
        self.seenterm = {}
	self.seenkind = {}
	self.c_const = []
	self.last_comment = None
    def readc(self, toks):
        while 1:
            tok = toks.read()
            if tok == None:
                return None
            if tok == '$(':
		self.last_comment = []
                while 1:
                    tok = toks.read_comment()
                    if tok == '$)':
                        break
		    else:
			self.last_comment.append(tok)
            else:
                return tok
    def readstat(self, toks):
        # read out to $. token; return list
        stat = []
        while 1:
            tok = self.readc(toks)
            if tok == None:
                raise 'EOF before $.'
            elif tok == '$.':
                break
            stat.append(tok)
        return stat
    def read(self, toks):
        self.fs.push()
        label = None
        while 1:
            tok = self.readc(toks)
            if tok == None or tok == '$}':
                break
            elif tok == '$c':
                for tok in self.readstat(toks):
                    self.fs.add_c(tok)
            elif tok == '$v':
                for tok in self.readstat(toks):
                    self.fs.add_v(tok)
            elif tok == '$f':
                stat = self.readstat(toks)
                if len(stat) != 2: raise '$f must have be length 2'
                if verbosity >= 15: print label, '$f', stat[0], stat[1], '$.'
                self.fs.add_f(stat[1], stat[0])
                if not label: raise '$f must have label'
                self.labels[label] = ('$f', stat[0], stat[1])
                label = None
		if not self.seenkind.has_key(stat[0]):
		    self.seenkind[stat[0]] = 1
		    print 'kind', sexp_to_string([stat[0]])
                if not self.seenvar.has_key(stat[1]):
                    self.seenvar[stat[1]] = stat[0]
                    print 'var', sexp_to_string([stat[0], stat[1]])
            elif tok == '$a':
                stat = self.readstat(toks)
                if not label: raise '$a must have label'
		cvlabel = self.labelmap.get(label, label)
                self.labels[cvlabel] = ('$a', self.fs.make_assertion(stat))
                self.a_to_gh(cvlabel, stat)
                label = None
            elif tok == '$e':
                stat = self.readstat(toks)
                self.fs.add_e(label, stat)
                if not label: raise '$e must have label'
                self.labels[label] = ('$e', stat)
                label = None
            elif tok == '$p':
                stat = self.readstat(toks)
                proof = None
                try:
                    i = stat.index('$=')
                    proof = stat[i + 1:]
                    stat = stat[:i]
                except ValueError:
                    raise '$p must contain proof after $='
                if not label: raise '$p must have label'
                if verbosity >= 1: print '# converting', label
#                self.verify(stat, proof)
                hyps = []
                fv = []
                for fr in self.fs.stack:
                    for i in range(len(fr.e)):
                        hyp = fr.e[i][1:]
                        fv.extend(self.find_vars(hyp))
                        hyps.append([fr.elabels[i], self.mm_to_sexp(hyp)])
                for l in proof:
                    step = self.labels.get(l, [''])
                    if step[0] == '$f':
                        v = step[2]
                        if not v in fv:
                            fv.append(v)
                dv = self.fs.get_dv(fv)
                gh_proof = self.to_gh(proof)
                self.n_gh_steps += len(gh_proof)
                ghlabel = thm_rename.get(label, label)
                gh_cmd = [ghlabel, dv, hyps, self.mm_to_sexp(stat[1:]), gh_proof]
                if stat[0] == '|-':
		    self.format_comment()
                    print 'thm', sexp_to_string(gh_cmd)
                self.labels[label] = ('$p', self.fs.make_assertion(stat))
                label = None
            elif tok == '$d':
                stat = self.readstat(toks)
                self.fs.add_d(stat)
            elif tok == '${':
                self.read(toks)
            elif tok[0] != '$':
                label = tok
            else:
                print 'tok:', tok
        self.fs.pop()
    def apply_subst(self, stat, subst):
        result = []
        for tok in stat:
            if subst.has_key(tok):
                result.extend(subst[tok])
            else:
                result.append(tok)
        if verbosity >= 20: print 'apply_subst', (stat, subst), '=', result
        return result
    def find_vars(self, stat):
        vars = []
        for x in stat:
            if not x in vars and self.fs.lookup_v(x):
                vars.append(x)
        return vars
    def verify(self, stat, proof):
        stack = []
        for label in proof:
            step = self.labels[label]
            if verbosity >= 10: print label, ':', step
            if step[0] == '$f':
                stack.append([step[1], step[2]])
            elif step[0] in ('$a', '$p'):
                (distinct, mand_var, hyp, result) = step[1]
                if verbosity >= 12: print (distinct, mand_var, hyp, result)
                npop = len(mand_var) + len(hyp)
                sp = len(stack) - npop
                if sp < 0: raise 'stack underflow'
                subst = {}
                for (k, v) in mand_var:
                    entry = stack[sp]
                    if entry[0] != k:
                        print (k, v), entry
                        raise "stack entry doesn't match mandatory var hyp"
                    subst[v] = entry[1:]
                    sp += 1
                if verbosity >= 15: print 'subst:', subst
                for x, y in distinct:
                    if verbosity >= 16:
                        print 'dist', x, y, subst[x], subst[y]
                    x_vars = self.find_vars(subst[x])
                    y_vars = self.find_vars(subst[y])
                    if verbosity >= 16:
                        print 'V(x) =', x_vars
                        print 'V(y) =', y_vars
                    for gam in x_vars:
                        for delt in y_vars:
                            if gam == delt:
                                raise "disjoint violation " + gam
                            x, y = gam, delt
                            if x > y:
                                x, y = y, x
                            if not self.fs.lookup_d(x, y):
                                raise "disjoint violation " + x + ", " + y
                for h in hyp:
                    entry = stack[sp]
                    subst_h = self.apply_subst(h, subst)
                    if entry != subst_h:
                        print 'st:', entry
                        print 'hy:', subst_h
                        raise "stack entry doesn't match hypothesis"
                    sp += 1
                del stack[len(stack) - npop:]
                stack.append(self.apply_subst(result, subst))
            elif step[0] == '$e':
                stack.append(step[1])
            if verbosity >= 12: print 'st:', stack
        if len(stack) != 1: raise 'stack has >1 entry at end'
        if stack[0] != stat: raise "assertion proved doesn't match"
    def to_gh(self, proof):
        stack = []
        gh_proof = []
        for label in proof:
            cvlabel = self.labelmap.get(label, label)
            step = self.labels[cvlabel]
            if verbosity >= 10: print label, ':', step
            if step[0] == '$f':
                stack.append(step[2])
            elif step[0] in ('$a', '$p'):
                self.n_mm_steps += 1
                (distinct, mand_var, hyp, result) = step[1]
                if verbosity >= 12: print (distinct, mand_var, hyp, result)
                npop = len(mand_var) + len(hyp)
                sp = len(stack) - npop
                if sp < 0: raise 'stack underflow'
                step = []
                mvs = map(lambda x: x[1], mand_var)
                hypvars = []
                for h in hyp:
                    for tok in h:
                        if tok in mvs and tok not in hypvars:
                            hypvars.append(tok)
                sortmvs = []
                for tok in result:
                    if tok in mvs and tok not in sortmvs:
                        sortmvs.append(tok)
                #print mvs, 'hypvars:', hypvars
                mvmap = {}
                for (k, v) in mand_var:
                    entry = stack[sp]
                    mvmap[v] = entry
                    sp += 1
                # ...distinct here
                for h in hyp:
                    entry = stack[sp]
                    step.append(entry)
                    #gh_proof.append(entry)
                    sp += 1
                del stack[len(stack) - npop:]
                for v in sortmvs:
                    if v not in hypvars:
                        step.append(mvmap[v])
                        if result[0] == '|-': gh_proof.append(mvmap[v])
                if result[0] == '|-':
                    step.append(thm_rename.get(label, label))
                    gh_proof.append(thm_rename.get(label, label))
                elif label != cvlabel:
                    step[0] = ['cv', step[0]]
                    if label != 'wsb':
                        step[1] = ['cv', step[1]]
                    step.insert(0, self.seenterm[cvlabel])
                elif self.seenterm.has_key(label):
                    step.insert(0, self.seenterm[label])
                else:
                    raise 'seenterm fail: ' + `result`
                stack.append(step)
            elif step[0] == '$e':
                stack.append(label)
                gh_proof.append(label)
            if verbosity >= 12: print 'st:', stack
        if len(stack) != 1: raise 'stack has >1 entry at end'
        return gh_proof
    def mm_to_sexp_rec(self, mm, i):
        tok = mm[i]
        i += 1
        (j, a) = self.mm_to_sexp_class(mm, i - 1)
        if a != None:
            (k, b) = self.mm_to_sexp_class(mm, j)
            if b != None:
                (k, c) = self.mm_to_sexp_class(mm, k)
                if c != None:
                    return (k, ['br', a, b, c])
            op = mm[j]
            j += 1
            if op in self.c_conn:
                (j, b) = self.mm_to_sexp_class(mm, j)
                if b == None:
                    raise 'expected rhs of c_conn ' + op
                return (j, [term_rename.get(op, op), a, b])
            elif op == ':':
                (j, b) = self.mm_to_sexp_class(mm, j)
                op += mm[j]
                if not op in (':-->', ':-1-1->', ':-onto->', ':-1-1-onto->'):
                    raise 'unknown function connective ' + op
                j += 1
                (j, c) = self.mm_to_sexp_class(mm, j)
                return (j, [op, a, b, c])
            elif op == 'Isom':
                (j, b) = self.mm_to_sexp_class(mm, j)
                if mm[j] != ',':
                    raise 'expected , in Isom'
                j += 1
                (j, c) = self.mm_to_sexp_class(mm, j)
                if mm[j] != '(':
                    raise 'expected ( in Isom'
                j += 1
                (j, d) = self.mm_to_sexp_class(mm, j)
                if mm[j] != ',':
                    raise 'expected , in Isom'
                j += 1
                (j, e) = self.mm_to_sexp_class(mm, j)
                if mm[j] != ')':
                    raise 'expected ) in Isom'
                j += 1
                return (j, [op, a, b, c, d, e])
            else:
                raise 'unknown class connective ' + op
        if tok == '-.':
            (i, result) = self.mm_to_sexp_rec(mm, i)
            return (i, ['-.', result])
        elif tok in ('A.', 'E.', 'E!', 'E*'):
            op = tok
            v = mm[i]
            i += 1
            if mm[i] == 'e.':
                i += 1
                (i, a) = self.mm_to_sexp_class(mm, i)
                (i, ph) = self.mm_to_sexp_rec(mm, i)
                return (i, [op + 'e.', v, a, ph])
            (i, ph) = self.mm_to_sexp_rec(mm, i)
            return (i, [op, v, ph])
        elif tok == '(':
            (i, a) = self.mm_to_sexp_rec(mm, i)
            op = mm[i]
            i += 1
            (i, b) = self.mm_to_sexp_rec(mm, i)
            if mm[i] == op:
                i += 1
                (i, c) = self.mm_to_sexp_rec(mm, i)
                if mm[i] != ')':
                    raise SyntaxError('expected )')
                i += 1
                return (i, [op + op, a, b, c])
            if mm[i] != ')':
                raise SyntaxError('expected )')
            i += 1
            return (i, [op, a, b])
        elif tok == '[':
            (i, a) = self.mm_to_sexp_class(mm, i)
            tok = mm[i]
            i += 1
            if tok == '/':
                v = mm[i]
                i += 1
                if mm[i] != ']':
                    raise 'expected ]'
                i += 1
                (i, ph) = self.mm_to_sexp_rec(mm, i)
                return (i, ['[/]', a, v, ph])
            else:
                raise 'unknown [ form ' + tok
        elif tok in self.c_pred:
            (i, a) = self.mm_to_sexp_class(mm, i)
            if a == None:
                raise 'expected class after ' + tok
            return (i, [tok, a])
        elif self.fs.lookup_v(tok) and self.fs.lookup_f(tok) == 'wff':
            return (i, tok)
        else:
            raise 'unknown wff ' + `mm[i:]`
                    

    def mm_to_sexp_class(self, mm, i):
        tok = mm[i]
        i += 1
        if tok in self.c_const:
            return (i, [term_rename.get(tok, tok)])
        elif tok == '(':
            (i, a) = self.mm_to_sexp_class(mm, i)
            if a == None:
                return (i, None)
            op = mm[i]
            if op in self.c_bin:
                i += 1
                (i, b) = self.mm_to_sexp_class(mm, i)
                if b == None:
                    raise 'expected rhs for ' + op
                if mm[i] != ')':
                    raise 'expected ) for c_bin ' + op
                i += 1
                return (i, [op, a, b])
            else:
                (i, b) = self.mm_to_sexp_class(mm, i)
                if b == None:
                    return (i, None)
                (i, c) = self.mm_to_sexp_class(mm, i)
                if c == None:
                    return (i, None)
                if mm[i] != ')':
                    return (i, None)
                i += 1
                return (i, ['opr', a, b, c])
        elif tok == '{':
            (i, a) = self.mm_to_sexp_class(mm, i)
            if a == None:
                raise 'expected class after {'
            tok = mm[i]
            i += 1
            if tok == '|':
                (i, ph) = self.mm_to_sexp_rec(mm, i)
                if mm[i] != '}':
                    raise 'expected }'
                i += 1
                if a[0] == 'cv':
                    return (i, ['{|}', a[1], ph])
                elif a[0] == '<,>':
                    if a[1][0] == '<,>':
                        if a[1][1][0] == 'cv' and a[1][2][0] == 'cv' and a[2][0] == 'cv':
                            return (i, ['{<<,>,>|}', a[1][1][1], a[1][2][1], a[2][1], ph])
                        
                    if a[1][0] != 'cv' or a[2][0] != 'cv':
                        raise 'unknown pair abstraction ' + `a`
                    return (i, ['{<,>|}', a[1][1], a[2][1], ph])
                else:
                    raise 'unknown abstraction form: ' + `a`
            elif tok == 'e.':
                (i, b) = self.mm_to_sexp_class(mm, i)
                if b == None:
                    raise 'expected class A in { x e. A | ph }'
                if mm[i] != '|':
                    raise 'expected | in { x e. A | ph }'
                i += 1
                (i, ph) = self.mm_to_sexp_rec(mm, i)
                if mm[i] != '}':
                    raise 'expected }'
                i += 1
                if a[0] == 'cv':
                    return (i, ['{e.|}', a[1], b, ph])
                else:
                    raise 'unknown abstraction form: ' + `a`
            elif tok == '}':
                return (i, ['{}', a])
            elif tok == ',':
                (i, b) = self.mm_to_sexp_class(mm, i)
                if b == None:
                    raise 'expected class B in { A , B }'
                if mm[i] == ',':
                    i += 1
                    (i, c) = self.mm_to_sexp_class(mm, i)
                    if mm[i] != '}':
                        raise 'expected } in { A , B , C }'
                    i += 1
                    return (i, ['{,,}', a, b, c])
                if mm[i] != '}':
                    raise 'expected } in { A , B }'
                i += 1
                return (i, ['{,}', a, b])
            else:
                raise 'unknown abstraction separator: ' + tok
        elif tok == '<.':
            (i, a) = self.mm_to_sexp_class(mm, i)
            if a == None:
                raise 'expected class after <.'
            if mm[i] != ',':
                raise 'expected , after <.'
            i += 1
            (i, b) = self.mm_to_sexp_class(mm, i)
            if mm[i] != '>.':
                raise 'expected >. after <.'
            i += 1
            return (i, ['<,>', a, b])
        elif tok == '[':
            (i, a) = self.mm_to_sexp_class(mm, i)
            if a == None:
                raise 'expected class after ['
            if mm[i] == ']':
                i += 1
                (i, r) = self.mm_to_sexp_class(mm, i)
                return (i, ['[]', a, r])
            return (i, None)
        elif tok == 'if':
            if mm[i] != '(':
                raise 'ifexpected ('
            i += 1
            (i, ph) = self.mm_to_sexp_rec(mm, i)
            if mm[i] != ',':
                raise 'if expected ,'
            i += 1
            (i, a) = self.mm_to_sexp_class(mm, i)
            if mm[i] != ',':
                raise 'if expected ,'
            i += 1
            (i, b) = self.mm_to_sexp_class(mm, i)
            if mm[i] != ')':
                raise 'if expected )'
            i += 1
            return (i, ['if', ph, a, b])
        elif tok == 'sup':
            if mm[i] != '(':
                raise tok + ' expected ('
            i += 1
            (i, a) = self.mm_to_sexp_class(mm, i)
            if mm[i] != ',':
                raise tok + ' expected ,'
            i += 1
            (i, b) = self.mm_to_sexp_class(mm, i)
            if mm[i] != ',':
                raise tok + ' expected ,'
            i += 1
            (i, r) = self.mm_to_sexp_class(mm, i)
            if mm[i] != ')':
                raise tok + ' expected )'
            i += 1
            return (i, [tok, a, b, r])
        elif tok == 'rec':
            if mm[i] != '(':
                raise tok + ' expected ('
            i += 1
            (i, f) = self.mm_to_sexp_class(mm, i)
            if mm[i] != ',':
                raise tok + ' expected ,'
            i += 1
            (i, a) = self.mm_to_sexp_class(mm, i)
            if mm[i] != ')':
                raise tok + ' expected )'
            i += 1
            return (i, [tok, f, a])
        elif tok in ('U.', '|^|'):
            (i, a) = self.mm_to_sexp_class(mm, i)
            return (i, [tok, a])
        elif tok in ('U_', '|^|_', 'X_'):
            (i, a) = self.mm_to_sexp_class(mm, i)
            if a[0] == 'cv' and mm[i] == 'e.':
                (j, b) = self.mm_to_sexp_class(mm, i + 1)
                if b != None:
                    (j, c) = self.mm_to_sexp_class(mm, j)
                    if c != None:
                        return (j, [tok, a[1], b, c])
        elif tok == '[_':
            (i, a) = self.mm_to_sexp_class(mm, i)
            tok = mm[i]
            i += 1
            if tok == '/':
                v = mm[i]
                i += 1
                if mm[i] != ']_':
                    raise 'expected ]_'
                i += 1
                (i, b) = self.mm_to_sexp_class(mm, i)
                return (i, ['[_/]_', a, v, b])
            else:
                raise 'unexpected [_ token ' + tok
        elif tok == 'sum_':
            k = mm[i]
            i += 1
            tok = mm[i]
            i += 1
            if tok == 'e.':
                (i, a) = self.mm_to_sexp_class(mm, i)
                (i, b) = self.mm_to_sexp_class(mm, i)
                return (i, ['sum_', k, a, b])
            else:
                raise 'unexpected sum_ token ' + tok
        elif tok in self.c_un:
            (i, a) = self.mm_to_sexp_class(mm, i)
            return (i, [tok, a])
        elif self.fs.lookup_v(tok):
            k = self.fs.lookup_f(tok)
            if k == 'class':
                return (i, tok)
            elif k == 'set':
                return (i, ['cv', tok])
        return (i, None)

    def mm_to_sexp(self, mm):
        if verbosity >= 20: print 'converting', mm
        (i, result) = self.mm_to_sexp_rec(mm, 0)
        if i < len(mm):
            raise SyntaxError('extra junk: ' + string.join(mm[i:]))
        return result

    def a_to_gh(self, label, stat):
        if stat[0] == '|-':
            # axiom or definition
            fv = self.find_vars(stat)
            hyps = []
            for fr in self.fs.stack:
                for i in range(len(fr.e)):
                    hyp = fr.e[i][1:]
                    fv.extend(self.find_vars(hyp))
                    hyps.append(self.mm_to_sexp(hyp))
            dv = self.fs.get_dv(fv)
            gh_cmd = [label, dv, hyps, self.mm_to_sexp(stat[1:])]
            print 'stmt', sexp_to_string(gh_cmd)
        else:
            # well-formedness definition
            kind = stat[0]
            if not self.seenkind.has_key(kind):
                self.seenkind[kind] = 1
                print 'kind', sexp_to_string([kind])
            if kind == 'wff':
                gh_exp = self.mm_to_sexp(stat[1:])
            elif kind == 'class':
		if len(stat) == 2 and not self.fs.lookup_v(stat[1]):
		    # automatically add nullary terms to grammar
		    self.c_const.append(stat[1])
                i, gh_exp = self.mm_to_sexp_class(stat, 1)
            else:
                print 'unknown kind:', kind
                print '# axiom:', label, stat
                return
            if gh_exp == None:
                print 'error parsing ' + string.join(stat[1:])
                raise 'parse error'
            gh_term = [gh_exp[0]]
            for arg in gh_exp[1:]:
                if type(arg) == type('var'):
                    k = self.seenvar[arg]
                elif arg[0] == 'cv':
                    k = 'class'
                else:
                    print 'unknown kind of arg:', arg
                gh_term.append(k)
	    if not self.seenterm.has_key(label):
		gh_cmd = [kind, gh_term]
		print 'term', sexp_to_string(gh_cmd)
		self.seenterm[label] = gh_term[0]

    def dump(self):
        print self.labels

    def format_math(self, mstr):
	# Convert a Metamath term to Barghest markup
	str = mstr.strip()
	l = str.split()
	try:
	    sexp = self.mm_to_sexp(l)
	    return '#' + sexp_to_string(sexp) + '#'
	except:
	    pass
	try:
	    # Sometimes Norm leaves out extra parens; add them and see if
	    # that fixes it.
	    sexp = self.mm_to_sexp(['('] + l + [')'])
	    return '#' + sexp_to_string(sexp) + '#'
	except:
	    pass
	try:
	    i, sexp = self.mm_to_sexp_class(l, 0)
	    if i == len(l) and sexp != None:
		if sexp[0] == 'cv':
		    sexp = sexp[1]
		return '#' + sexp_to_string(sexp) + '#'
	except:
	    pass
	try:
	    i, sexp = self.mm_to_sexp_class(['('] + l + [')'], 0)
	    if i == len(l) + 2 and sexp != None:
		return '#' + sexp_to_string(sexp) + '#'
	except:
	    pass
	if len(str) == 0: str = '@@@' + mstr
	return '{{{' + str + '}}}'

    def format_comment(self):
	# Convert Metamath markup to Barghest markup
	if self.last_comment == None:
	    return
	print
	premode = False
	mode = 'n'
	retab = {'n': re.compile(r'(?<!\S)[_\[]|~~?|``?'),
		 'u': re.compile(r'_|~~?|``?'),
		 'm': re.compile(r'``?')}
	lab_re = re.compile(r'\s*(\S+)')
	oppunct_re = re.compile(r' [\"\(] $')
	clpunct_re = re.compile(r' [\"\.,;\)\?!:]')
	for line in self.last_comment:
	    if premode and line.strip() == '</PRE>':
		print '# }}}'
		premode = False
	    elif premode:
		print '# ' + line
	    elif not premode and line.strip() == '<PRE>':
		print '# {{{'
		premode = True
	    else:
		rline = ''
		pos = 0
		while pos < len(line):
		    m = retab[mode].search(line, pos)
		    if m:
			if mode != 'm':
			    rline += line[pos:m.start()]
			else:
			    mathstr += line[pos:m.start()]
			g = m.group()
			#print line
			#print ' ' * m.start() + g
			mend = m.end()
			if g == '`':
			    pos = mend
			    cl_m = clpunct_re.match(line, pos)
			    if mode == 'm':
				rline += self.format_math(mathstr)
				mode = 'n'
				if cl_m:
				    # skip whitespace before close punct
				    pos += 1
			    else:
				if oppunct_re.search(rline):
				    rline = rline[:-1]
				mode = 'm'
				mathstr = ''
			elif g == '``':
			    if mode == 'm':
				mathstr += '`'
			    else:
				rline += '`'
			    pos = mend
			elif g == '~':
			    m = lab_re.search(line, mend)
			    if m:
				if oppunct_re.search(rline):
				    rline = rline[:-1]
				label = m.group(1)
				label = label.replace('~~', '~')
				rline += '[[' + label + ']]'
				pos = m.end()
				if clpunct_re.match(line, pos):
				    # skip whitespace before close punct
				    pos += 1
			elif g == '~~':
			    rline += '~'
			    pos = mend
			elif g == '_':
			    mode = {'n': 'u', 'u': 'n'}[mode]
			    rline += '//'
			    pos = mend
			elif g == '[':
			    rline += '[bib/'
			    pos = mend
			if pos < mend:
			    rline += g
			    pos = mend
		    else:
			if mode != 'm':
			    rline += line[pos:]
			else:
			    mathstr += line[pos:]
			break
		print '#', rline
	self.last_comment = None

if __name__ == '__main__':
    import sys
    mm = MM()
    state = 0
    while 1:
        line = sys.stdin.readline()
        line = line.rstrip('\r\n')
        if state == 0 and len(line) >=6 and line[:6] == 'set.mm':
            print '#', line
            state = 1
        elif state == 1:
            if len(line) >= 5 and line[:5] == '=-=-=':
                state = 2
            else:
                print '#', line
        elif state == 2:
            if line == '$)':
                break
    mm.read(toks(sys.stdin))
    print '# %d Metamath steps converted to %d Ghilbert steps' % (mm.n_mm_steps, mm.n_gh_steps)
