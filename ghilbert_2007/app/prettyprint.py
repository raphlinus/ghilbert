import sys

import scanner, verify

def read_sexp_echo(scanner, os = None):
    while 1:
	tok = scanner.get_tok()
	if tok == None:
	    return None
	if os:
	    os.write(tok[-1])
	if tok == '(':
	    result = []
	    while 1:
		subsexp = read_sexp_echo(scanner, os)
		if subsexp == ')':
		    break
		elif subsexp == None:
		    raise SyntaxError('eof inside sexp')
		result.append(subsexp)
	    return result
	elif tok[0] != 'white':
	    return tok[-1]

def prettyprint_term(term, width = 60):
    if type(term) == type(''):
	return term
    else:
	subterms = []
	long = False
	for x in term:
	    st_fmt = prettyprint_term(x, width)
	    subterms.append(st_fmt)
	    long = long or type(st_fmt) == type([])
	if not long:
	    str = '(' + ' '.join(subterms) + ')'
	    if len(str) <= width or len(term) < 2: return str
	result = '('
	for i in range(len(term)):
	    st = subterms[i]
	    if (type(term[i]) == type('') or i < 2) and type(st) == type('') and type(result) == type('') and len(result) + len(st) + 2 <= width:
		if i: result += ' '
		result += st
	    else:
		if type(result) == type(''):
		    result = [result]
		if type(st) == type(''):
		    result.append('  ' + st)
		else:
		    for l in st:
			result.append('  ' + l)
	result[-1] = result[-1] + ')'
	return result

def writeslug(slug, os, pref, pref2 = None):
    if type(slug) == type(''):
	os.write(pref + slug)
    else:
	for ln in slug:
	    os.write(pref + ln)
	    if pref2 != None: pref = pref2

def prettyprint_thm(vg, sc, os, width = 60):
    while 1:
	tok = sc.get_tok()
	if tok == '(':
	    break
	elif tok[0] != 'white':
	    raise VerifyError('thm expects open paren')
    os.write(' (')
    label = read_sexp_echo(sc, os)
    dv = read_sexp_echo(sc, os)
    hyps = read_sexp_echo(sc)
    for i in range(len(hyps)):
	st = prettyprint_term(hyps[i], width)
	if i == 0: pref = '\n  ('
	else: pref = '\n   '
	writeslug(st, os, pref, '\n   ')
    if len(hyps):
	os.write(')')
    else:
	os.write(' ()')
    stat = read_sexp_echo(sc)
    writeslug(prettyprint_term(stat, width), os, '\n  ')
    while 1:
	tok = sc.get_tok()
	if tok == '(':
	    break
	elif tok[0] != 'white':
	    raise VerifyError('thm expects open paren for proof')
    os.write('\n  (')
    hypmap = {}
    for hyp in hyps:
	hypmap[hyp[0]] = hyp[1]
    proofctx = verify.ProofCtx()
    queue = {}
    stacklev = 0
    while 1:
	tok = sc.get_tok()
	if tok == ')':
	    break
	elif tok == '(':
	    step = []
	    while 1:
		subsexp = read_sexp_echo(sc)
		if subsexp == ')':
		    break
		step.append(subsexp)
	elif tok[0] == 'white':
	    step = None
	else:
	    step = tok[-1]
	if step != None:
	    try:
		vg.check_proof_step(hypmap, step, proofctx)
	    except verify.VerifyError, x:
	    #x.step = (step_ix, proof)
		x.stack = proofctx.stack
		x.label = label
		raise x
	    lastlev = stacklev
	    stacklev = len(proofctx.stack) + len(proofctx.mandstack)
	    st = prettyprint_term(step, width)
	    if type(st) == type(''):
		attempt = ''
		for lev in range(stacklev - 1, lastlev):
		    if queue.has_key(lev) and type(queue[lev]) == type(''):
			attempt += queue[lev] + ' '
		    else:
			attempt = None
			break
		if attempt != None:
		    attempt += st
	    else:
		attempt = None
	    #print '[', `attempt`,  queue, ']'
	    if attempt != None and len(attempt) <= width:
		for lev in range(stacklev - 1, lastlev):
		    del queue[lev]
		queue[stacklev - 1] = attempt
	    else:
		for lev in range(lastlev):
		    if queue.has_key(lev):
			writeslug(queue[lev], os, '\n   ' + '  ' * lev)
			del queue[lev]
		queue[stacklev - 1] = st
	    #writeslug(st, os, '\n ' + '  ' * stacklev)
    writeslug(queue[0], os, '\n   ')
    while 1:
	tok = sc.get_tok()
	if tok == ')':
	    break
	elif tok[0] != 'white':
	    raise VerifyError('thm expects close paren')
    os.write('\n))')
    vg.add_assertion('thm', label, dv, map(lambda x: x[1], hyps), stat, vg.syms)

def prettyprint_stmt(vg, sc, os, width = 60):
    while 1:
	tok = sc.get_tok()
	if tok == '(':
	    break
	elif tok[0] != 'white':
	    raise VerifyError('stmt expects open paren')
    os.write(' (')
    label = read_sexp_echo(sc, os)
    dv = read_sexp_echo(sc, os)
    hyps = read_sexp_echo(sc)
    for i in range(len(hyps)):
	st = prettyprint_term(hyps[i], width)
	if i == 0: pref = '\n  ('
	else: pref = '\n   '
	writeslug(st, os, pref, '\n   ')
    if len(hyps):
	os.write(')')
    else:
	os.write(' ()')
    stat = read_sexp_echo(sc)
    writeslug(prettyprint_term(stat, width), os, '\n  ')
    while 1:
	tok = sc.get_tok()
	if tok == ')':
	    break
	elif tok[0] != 'white':
	    raise VerifyError('stmt expects close paren')
    os.write('\n)')

def prettyprint(fn):
    os = sys.stdout
    sc = scanner.Scanner(file(fn))
    vg = verify.VerifyGh()
    while 1:
	cmd = read_sexp_echo(sc, os)
	if cmd == None:
	    break
	elif cmd == 'thm':
	    prettyprint_thm(vg, sc, os, 60)
	elif cmd == 'stmt':
	    prettyprint_stmt(vg, sc, os, 60)
	else:
	    arg = read_sexp_echo(sc, os)
	    if cmd == 'param':
		vg.do_cmd('import', arg)
	    elif cmd == 'kind':
		vg.kinds[arg[0]] = arg[0]
	    elif cmd == 'term':
		pass
	    else:
		vg.do_cmd(cmd, arg)

if __name__ == '__main__':
    prettyprint(sys.argv[1])
