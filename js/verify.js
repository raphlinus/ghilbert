// JavaScript implementation of Ghilbert verifier
// by Raph Levien, 2009
// Apache 2 license

// Put everything into a namespace defined by one variable.
if (typeof GH == 'undefined') {
  var GH = {};
}

GH.Scanner = function (lines) {
    this.lines = lines;
    this.lineno = 0;
    this.toks = [];
    this.tokix = 0;
}

GH.Scanner.prototype.get_tok = function() {
    while (this.tokix >= this.toks.length) {
	if (this.lineno == this.lines.length) {
	    return null;
	}
	var line = this.lines[this.lineno];
	this.lineno++;
	line = line.split('#')[0];
	line = line.replace(/\(|\)/g, ' $& ');
	this.toks = line.split(/ +/);
	this.tokix = this.toks[0] == '' ? 1 : 0;
	if (this.toks[this.toks.length - 1] == '') { this.toks.pop(); }
    }
    var result = this.toks[this.tokix];
    this.tokix++;
    return result;
};

GH.read_sexp = function(scanner) {
    while (1) {
	var tok = scanner.get_tok();
	if (tok === null) {
	    return null
	}
	if (tok == '(') {
	    var result = [];
	    while (1) {
		var subsexp = GH.read_sexp(scanner);
		if (subsexp == ')') {
		    break;
		} else if (subsexp == null) {
		    throw 'eof inside sexp';
		}
		result.push(subsexp);
	    }
	    return result;
	} else {
	    return tok;
	}
    }
};

GH.sexp_to_string = function(sexp) {
    if (typeof sexp == 'string') {
	return sexp;
    } else {
	// map would of course be shorter, but how available is it?
	var result = [];
	for (var i = 0; i < sexp.length; i++) {
	    result.push(GH.sexp_to_string(sexp[i]));
	}
    }
    return '(' + result.join(' ') + ')';
};

// Similar semantics as Python's os.path.split
GH.pathsplit = function(path) {
    var i = path.lastIndexOf('/');
    if (i == -1) {
	return ['', path];
    } else if (i == 0) {
	return ['/', path.slice(1)];
    } else {
	return [path.slice(0, i), path.slice(i + 1)];
    }
};

// Similar semantics as Python's os.path.join. Could be vararg, but we only use
// with 2.
GH.pathjoin = function(path1, path2) {
    if (path2.charAt(0) == '/' || path1.length == 0) {
	return path2;
    } else if (path1.charAt(path1.length - 1) == '/') {
	return path1 + path2;
    } else {
	return path1 + '/' + path2;
    }
};

// Is there not a builtin JS technique for this?
GH.sexp_equals = function(a, b) {
    if (typeof a == 'undefined') {
	throw 'whoa!'
    }
    if (typeof a == 'string') return a == b;
    if (typeof b == 'string' || a.length != b.length) return false;
    for (var i = 0; i < a.length; i++) {
	if (!GH.sexp_equals(a[i], b[i])) return false;
    }
    return true;
};

GH.XhrUrlCtx = function (repobase, basefn) {
    this.repobase = repobase;
    this.base = GH.pathsplit(basefn)[0];
};

GH.XhrUrlCtx.prototype.resolve = function (url) {
    var x = new XMLHttpRequest();
    // Sync is bad, it blocks the ui, but async is more complicated...
    if (url.slice(0, 7) == 'http://') {
	// absolute url, no change
    } else if (url.charAt(0) == '/') {
	url = GH.pathjoin(this.repobase, url.slice(1));
    } else {
	url = GH.pathjoin(this.base, url);
    }
    x.open('GET', url, false);
    x.overrideMimeType("text/plain");
    x.send(null);
    return x.responseText;
};

GH.ProofCtx = function(fvvarmap) {
    this.stack = [];
    this.mandstack = [];
    this.fvvarmap = fvvarmap;
};

GH.VerifyCtx = function(urlctx, run) {
    this.kinds = {};
    this.terms = {};
    this.syms = {};
    this.interfaces = {};
    this.urlctx = urlctx;
    this.run = run;
};

GH.VerifyCtx.prototype.add_sym = function(label, val) {
    if (label in this.syms) {
	throw 'Symbol ' + label + ' already defined';
    }
    this.syms[label] = val;
};

GH.VerifyCtx.prototype.add_kind = function(kind, val) {
    if (kind in this.kinds) {
	throw 'Kind ' + kind + ' already defined';
    }
    this.kinds[kind] = val;
};

GH.VerifyCtx.prototype.get_kind = function(kind) {
    if (kind in this.kinds) {
	return this.kinds[kind];
    } else {
	throw 'Kind not known: ' + kind;
    }
};

GH.VerifyCtx.prototype.add_term = function(label, kind, argkinds, freemap) {
    if (label in this.terms) {
	throw 'Term ' + label + ' already defined';
    }
    this.terms[label] = [kind, argkinds, freemap];
};

GH.VerifyCtx.prototype.add_assertion = function(kw, label, fv, hyps, concl, syms) {
    var mand = this.allvars(concl);
    for (var i = 0; i < hyps.length; i++) {
	var vars = this.allvars(hyps[i]);
	for (var j = 0; j < vars.length; j++) {
	    var ix = mand.indexOf(vars[j]);
	    if (ix >= 0) {
		mand.splice(ix, 1);
	    }
	}
    }
    this.add_sym(label, [kw, fv, hyps, concl, mand, syms]);
};

GH.VerifyCtx.prototype.allvars = function(exp) {
    var fv = [];
    function allvars_rec(exp) {
	if (typeof exp == 'string') {
	    if (fv.indexOf(exp) == -1) {
		fv.push(exp);
	    }
	} else {
	    for (var i = 1; i < exp.length; i++) {
		allvars_rec(exp[i]);
	    }
	}
    }
    allvars_rec(exp);
    return fv;
};

GH.VerifyCtx.prototype.free_in = function(v, term, fvvars) {
    if (typeof term == 'string') {
	var tvar = this.syms[term];
	if (tvar[0] == 'var' || fvvars === null) {
	    return v == term;
	}
	return !term in fvvars;
    } else {
	var freemap = this.terms[term[0]][2];
	var subterms = term.slice(1);
	for (var fv in freemap) {
	    if (term[fv * 1 + 1] == v) {
		subterms = [];
		for (var i in freemap[fv]) {
		    subterms.push(term[i + 1]);
		}
	    }
	}
	for (var i = 0; i < subterms.length; i++) {
	    if (this.free_in(v, subterms[i], fvvars)) {
		return true;
	    }
	}
	return false;
    }
};

GH.VerifyCtx.prototype.kind_of = function(exp, syms) {
    if (typeof exp == 'string') {
	if (syms === undefined) {
	    syms = this.syms;
	}
	var v = syms[exp];
	if (v[0] != 'var' && v[0] != 'tvar') {
	    throw 'Expression not a var: ' + exp;
	}
	return this.kinds[v[1]];
    } else {
	if (exp.length == 0) {
	    throw "Term can't be empty list";
	} else if (typeof exp[0] != 'string') {
	    throw 'Term must be id';
	} else if (!(exp[0]) in this.terms) {
	    throw 'Term ' + exp[0] + ' not known';
	}
	var v = this.terms[exp[0]];
	if (exp.length - 1 != v[1].length) {
	    throw 'Arity mismatch: ' + exp[0] + ' has arity ' + v[1].length + ' but was given ' + (exp.length - 1);
	}
	for (var i = 0; i < exp.length - 1; i++) {
	    var child_kind = this.kind_of(exp[i + 1], syms);
	    if (child_kind != this.kinds[v[1][i]]) {
		throw 'Kind mismatch';
	    }
	}
	return this.kinds[v[0]];
    }
};

GH.VerifyCtx.prototype.do_cmd = function(cmd, arg) {
    if (cmd == 'import') {
	var iname = arg[0];
	var url = arg[1];
	var params = arg[2];
	var prefix = arg[3];
	if (prefix.length < 2 || prefix.charAt(0) != '"' || prefix.charAt(prefix.length - 1) != '"') {
	    throw 'Namespace prefix must be enclosed in quotes';
	}
	prefix = prefix.substring(1, prefix.length - 1);
	var importctx = new GH.ImportCtx(this, prefix);
	this.run(this.urlctx, url, importctx);
    } else if (cmd == 'var' || cmd == 'tvar') {
	var kind = this.get_kind(arg[0]);
	for (var i = 1; i < arg.length; i++) {
	    this.add_sym(arg[i], [cmd, kind]);
	}
    } else if (cmd == 'kindbind') {
	this.add_kind(arg[1], this.get_kind(arg[0]));
    } else if (cmd == 'thm') {
	if (arg.length < 5) {
	    throw 'Expected at least 5 args to thm';
	}
	var label = arg[0];
	var fv = arg[1];
	var hyps = arg[2];
	var stmt = arg[3];
	var proof = arg.slice(4);
	log('checking ' + label);
	this.check_proof(label, fv, hyps, stmt, proof);
	var new_hyps = [];
	for (i = 1; i < hyps.length; i += 2) {
	    new_hyps.push(hyps[i]);
	}
	this.add_assertion('thm', label, fv, new_hyps, stmt, this.syms);
    }
};

GH.VerifyCtx.prototype.check_proof = function(label, fv, hyps, stmt, proof) {
    if (hyps.length & 1) {
	throw 'hyp list must be even';
    }
    var fvmap = {};
    var stmtvars = this.allvars(stmt);
    for (var i = 0; i < stmtvars.length; i++) {
	var v = stmtvars[i];
	if (!(v in this.syms)) {
	    throw 'Variable not found: ' + v;
	}
	if (this.syms[v][0] == 'var') {
	    fvmap[v] = {};
	}
    }
    var hypmap = {};
    for (var i = 0; i < hyps.length; i += 2) {
	if (typeof hyps[i] != 'string') {
	    throw 'Hyp label must be string';
	}
	hypmap[hyps[i]] = hyps[i + 1];
	var vars = this.allvars(hyps[i + 1]);
	for (var j = 0; j < vars.length; j++) {
	    var v = vars[j];
	    if (!(v in this.syms)) {
		throw 'Variable not found: ' + v;
	    }
	    if (this.syms[v][0] == 'var') {
		fvmap[v] = {};
	    }
	}
	this.kind_of(hyps[i + 1]);
    }
    for (var i = 0; i < fv.length; i++) {
	var clause = fv[i];
	if (typeof clause == 'string' || clause.length == 0) {
	    throw 'Each fv clause must be list of vars';
	}
	var tvar = clause[0];
	if (typeof tvar != 'string') {
	    throw 'Var in fv clause must be string';
	}
	if (!(tvar in this.syms && this.syms[tvar][0] == 'tvar')) {
	    throw 'First var in fv clause must be tvar: ' + tvar;
	}
	for (var j = 1; j < clause.length; j++) {
	    var v = clause[j];
	    if (typeof v != 'string') {
		throw 'Var in fv clause must be string';
	    }
	    if (!(v in this.syms && this.syms[v][0] == 'var')) {
		throw 'Subsequent var in fv clause must be var: ' + v;
	    }
	    if (!(v in fvmap)) {
		throw 'Spurious var in fv list: ' + v;
	    }
	    fvmap[v][tvar] = 0;
	}
    }
    var proofctx = new GH.ProofCtx(fvmap);
    for (var i = 0; i < proof.length; i++) {
	this.check_proof_step(hypmap, proof[i], proofctx);
    }
    if (proofctx.mandstack.length != 0) {
	throw 'Extra mand hyps on stack at end of proof';
    }
    if (proofctx.stack.length != 1) {
	throw 'Stack must have one term at end of proof';
    }
    if (!GH.sexp_equals(proofctx.stack[0], stmt))
	throw 'Stack has ' + GH.sexp_to_string(proofctx.stack[0]) + ' wanted ' + GH.sexp_to_string(stmt);
};

GH.VerifyCtx.prototype.check_proof_step = function(hypmap, step, proofctx) {
    if (typeof step != 'string') {
	var kind = this.kind_of(step);
	proofctx.mandstack.push([['tvar', kind], step]);
    } else if (step in hypmap) {
	if (proofctx.mandstack.length != 0) {
	    throw 'Hyp expected no mand hyps, got ' + proofctx.mandstack.length;
	}
	proofctx.stack.push(hypmap[step]);
    } else {
	if (!(step in this.syms)) {
	    throw 'Unknown proof step';
	}
	var v = this.syms[step];
	if (v[0] == 'var' || v[0] == 'tvar') {
	    proofctx.mandstack.push([v, step]);
	} else if (v[0] == 'stmt' || v[0] == 'thm') {
	    var fv = v[1];
	    var hyps = v[2];
	    var concl = v[3];
	    var mand = v[4];
	    var syms = v[5];
	    if (mand.length != proofctx.mandstack.length) {
		throw 'Expected ' + mand.length + ' mand hyps, got ' + proofctx.mandstack.length;
	    }
	    var env = {};
	    for (var i = 0; i < mand.length; i++) {
		var mv = mand[i];
		var tkind = syms[mv];
		var el = proofctx.mandstack[i];
		if (el[0][1] != tkind[1]) {
		    throw 'Kind mismatch for ' + mv + ': expected ' + tkind[1] + ' got ' + el[0][1];
		}
		this.match(mv, el[1], env);
	    }
	    var sp = proofctx.stack.length - hyps.length;
	    if (sp < 0) {
		throw 'Stack underflow';
	    }
	    for (i = 0; i < hyps.length; i++) {
		var el = proofctx.stack[sp + i];
		this.match(hyps[i], el, env);
	    }
	    for (i = 0; i < fv.length; i++) {
		var tvar = fv[i][0];
		for (var j = 1; j < fv[i].length; j++) {
		    var bv = fv[i][j];
		    if (this.free_in_proof(env[bv], env[tvar], proofctx)) {
			throw 'Expected ' + env[bv] + ' not free in ' + GH.sexp_to_string(env[tvar]);
		    }
		}
	    }
	    var invmap = {};
	    for (v in env) {
		var exp = env[v];
		if (syms[v][0] == 'var') {
		    if (typeof exp != 'string') {
			throw 'Expected binding variable for ' + v;
		    }
		    if (this.syms[exp][0] != 'var') {
			throw 'Expected binding variable for ' + v + '; ' + exp + ' is term variable';
		    }
		    if (exp in invmap) {
			throw 'Binding variables ' + invmap[exp] + ' and ' + v + ' both map to ' + exp;
		    }
		    invmap[exp] = v;
		}
	    }
	    var result = this.apply_subst(concl, env);
	    proofctx.stack.splice(sp);
	    proofctx.stack.push(result);
	    proofctx.mandstack = [];
	}
    }
};

GH.VerifyCtx.prototype.free_in_proof = function(v, term, proofctx) {
    return this.free_in(v, term, proofctx.fvvarmap[v] || null);
};

GH.VerifyCtx.prototype.match = function(templ, exp, env) {
    if (typeof templ == 'string') {
	if (templ in env) {
	    if (!GH.sexp_equals(exp, env[templ])) {
		log(GH.sexp_to_string(exp) + " -- " + GH.sexp_to_string(env[templ]));
		throw 'Unification error';
	    }
	} else {
	    env[templ] = exp;
	}
    } else {
	if (typeof exp == 'string') {
	    throw 'Unification error, expected ' + GH.sexp_to_string(templ) + ' got ' + exp;
	}
	if (templ[0] != exp[0]) {
	    throw 'Unification error, expected ' + templ[0] + ' got ' + exp[0];
	}
	if (exp.length != templ.length) {
	    throw 'Term ' + templ[0] + ' expects arity ' + templ.length + ' got ' + exp.length;
	}
	for (var i = 1; i < templ.length; i++) {
	    this.match(templ[i], exp[i], env);
	}
    }
};

GH.VerifyCtx.prototype.apply_subst = function(templ, env) {
    if (typeof templ == 'string') {
	return env[templ];
    } else {
	var result = [templ[0]];
	for (var i = 1; i < templ.length; i++) {
	    result.push(this.apply_subst(templ[i], env));
	}
    }
    return result;
};

GH.map_syms = function(sexp, map) {
    if (typeof sexp == 'string') {
	return sexp;
    } else {
	var result = [map[sexp[0]]];
	for (var i = 1; i < sexp.length; i++) {
	    result.push(GH.map_syms(sexp[i], map));
	}
    }
    return result;
};

GH.ImportCtx = function(verify, prefix) {
    this.verify = verify;
    this.prefix = prefix;
    this.vars = {};
    this.term_map = {};
};

GH.ImportCtx.prototype.get_kind = function(rawkind) {
    return this.verify.get_kind(this.prefix + rawkind);
};

GH.ImportCtx.prototype.do_cmd = function(cmd, arg) {
    if (cmd == 'kind') {
	if (typeof arg == 'string' || arg.length != 1) {
	    throw 'Kind takes one arg';
	}
	if (typeof arg[0] != 'string') {
	    throw 'Kind must be string';
	}
	var kind = this.prefix + arg[0];
	this.verify.add_kind(kind, kind);
    } else if (cmd == 'var' || cmd == 'tvar') {
	if (typeof arg == 'string') {
	    throw 'Args must be list';
	}
	var kind = this.get_kind(arg[0]);
	for (var i = 1; i < arg.length; i++) {
	    var v = arg[i];
	    if (v in this.vars) {
		throw 'Variable ' + v + ' already defined';
	    }
	    this.vars[v] = [cmd, kind];
	}
    } else if (cmd == 'term') {
	if (typeof arg == 'string') {
	    throw 'Args must be list';
	}
	var kind = this.get_kind(arg[0]);
	if (typeof arg[1] == 'string') {
	    throw 'Term arg must be list';
	}
	var local_termname = arg[1][0];
	var termname = this.prefix + local_termname;
	var argkinds = [];
	var freemap = {};
	var invmap = {};
	for (var i = 1; i < arg[1].length; i++) {
	    var v = arg[1][i];
	    var vv = this.vars[v];
	    if (v in invmap) {
		throw 'Variable ' + v + ' not unique';
	    }
	    invmap[v] = i - 1;
	    argkinds.push(vv[1]);
	    if (vv[0] == 'var') {
		freemap[i - 1] = [];
	    }
	}
	for (i = 2; i < arg.length; i++) {
	    var freespec = arg[i];
	    var bv = invmap[freespec[0]];
	    if (!(bv in freemap)) {
		throw 'Binding variable ' + bv + ' not found';
	    }
	    if (freemap[bv].length) {
		throw 'More than one freespec for ' + bv;
	    }
	    freemap[bv] = [];
	    for (var j = 1; j < freespec.length; j++) {
		freemap[bv].push(invmap[freespec[j]]);
	    }
	}
	this.verify.add_term(termname, kind, argkinds, freemap);
	this.term_map[local_termname] = termname;
    } else if (cmd == 'stmt') {
	if (typeof arg == 'string') {
	    throw 'Args must be list';
	}
	if (arg.length != 4) {
	    throw 'Stmt takes 4 args';
	}
	var local_label = arg[0];
	var fv = arg[1];
	var local_hyps = arg[2];
	var local_stmt = arg[3];
	var label = this.prefix + local_label;
	var stmt = GH.map_syms(local_stmt, this.term_map);
	var hyps = [];
	for (var i = 0; i < local_hyps.length; i++) {
	    hyps.push(GH.map_syms(local_hyps[i], this.term_map));
	}
	// todo: verify kind consistency
	this.verify.add_assertion('stmt', label, fv, hyps, stmt, this.vars);
    } else if (cmd == 'param') {
	// todo: nyi
    } else {
	throw 'Unknown interface command ' + cmd;
    }
};
