// JavaScript implementation of Ghilbert verifier
// by Raph Levien, 2009
// Apache 2 license

// Put everything into a namespace defined by one variable.
if (typeof(global) !== 'undefined') {
    var GH = global.GH;
}
if (typeof GH == 'undefined') {
  var GH = {};
}

/**
 * Like the regular typeof, but returns 'string' for Objects which are
 * instanceof String.  This allows us to extend String objects with
 * more properties, since JS does not allow you to set properties on
 * strings.
 */
GH.typeOf = function(obj) {
    if (obj instanceof String) {
        return 'string';
    }
    return typeof obj;
};

GH.Scanner = function (lines) {
    this.lines = lines;
    this.lineno = 0;
    this.toks = [];
    this.tokix = 0;

	this.styleScanner = new GH.StyleScanner();
};

GH.styling = function(table, title, suggest, filename, thmNumber, isAxiom) {
	this.table = table;
	this.title = title;
	this.filename = filename;
	this.thmNumber = thmNumber;
	this.isAxiom = isAxiom;
	// Remove the quotation marks from the suggestion names.
	if (suggest) {
		for (var i = 0; i < suggest.length; i++) {
			var suggestParameter = '';
			var lastToken = true;
			while (suggest[i].length > 1) {
				if (!lastToken) {
					suggestParameter = ' ' + suggestParameter;
				}
				lastToken = false;
				suggestParameter = suggest[i].pop() + suggestParameter;
			}
			var splitParameters = suggestParameter.split('\'');
			var parameters = [];
			for (var j = 1; j < splitParameters.length; j += 2) {
				suggest[i].push(splitParameters[j]);
			}
		}
	}
	this.suggest = suggest;
};

GH.StyleScanner = function() {
	this.styleMode = GH.StyleScanner.modeTypes.NONE;
	this.table = null;
	this.title = '';
	this.summary = '';
	this.suggest = null;
	this.leftColumns = 0;
	this.color = '';
	// Whether or not this is an axiom having no proof.
	this.isAxiom = false;
	this.context = '';
};

// Global variables are bad.
GH.StyleScanner.thmCounter = 0;

GH.StyleScanner.modeTypes = {
	NONE: 0,
	TABLE: 1,
	TITLE: 2,
	SUGGEST: 3,
	SUGGEST_FUNC: 4,
	SUMMARY: 5,
	CONTEXT: 6
};

GH.StyleScanner.prototype.read_column_style = function(tok) {
	if (tok == '') {
		return;
	} else if (tok == '(') {
		var newTableExpression = new GH.tableExpression(this.table, null, this.leftColumns, this.color);
		this.table.children.push(newTableExpression);
		this.table = newTableExpression;
		this.leftColumns = 0;
		this.color = '';
	} else if (tok == ')') {
		this.table = this.table.parent;
	} else if (tok == '[') {
		this.leftColumns++;
	} else if (tok == ']') {
		this.table.addRightColumn();
	} else if (tok == '<r>') {
		this.color = 'red';
	} else if (tok == '<m>') {
		this.color = 'magenta';
	} else if (tok == '<b>') {
		this.color = 'blue';
	} else if (tok == '<c>') {
		this.color = 'cyan';
	} else if (tok == '<g>') {
		this.color = 'green';
	} else if (tok == '<k>') {
		this.color = 'black';
	} else {
		this.table.addExpression(tok, this.leftColumns, this.color);
		this.leftColumns = 0;
		this.color = '';
	}
};

GH.StyleScanner.prototype.get_styling = function(filename) {
	var tableStyle = null;
	if (this.table) {
		tableStyle = this.table.output();
		tableStyle.splice(0, 1);
	}
	return new GH.styling(
		tableStyle, this.title, this.suggest, filename, GH.StyleScanner.thmCounter, this.isAxiom);
};

GH.StyleScanner.prototype.clear = function() {
	this.table = null;
	this.title = '';
	this.suggest = null;
	this.isAxiom = false;
	GH.StyleScanner.thmCounter++;
}

GH.StyleScanner.prototype.addSuggestToken = function(tok) {
	var modeTypes = GH.StyleScanner.modeTypes;
	if (tok == '(') {
		this.styleMode = modeTypes.SUGGEST_FUNC;
	} else if (tok == ')') {
		this.styleMode = modeTypes.SUGGEST;
	} else {
		if (this.styleMode == modeTypes.SUGGEST) {
			this.suggest.push([]);
		}
		this.suggest[this.suggest.length - 1].push(tok);
	}

};

GH.StyleScanner.prototype.get_context = function() {
	return this.context;
};

GH.StyleScanner.prototype.read_styling = function(line) {
	var splitLine = line.split('##');
	if (splitLine.length != 2) {
		return;
	}
	line = splitLine[1];
	var initialLength = this.table ? this.table.length : 0;
	var styleModeTypes = GH.StyleScanner.modeTypes;
	var toks = line.split(/[ \t]+/);
	for (var i = 0; i < toks.length; i++) {
		var tok = toks[i];
		if (tok == '<table>') {
			this.styleMode = styleModeTypes.TABLE;
			this.table = new GH.tableExpression(null, 'root', 0, '');
		} else if (tok == '</table>') {
			// TODO: Add test that there are an equal number of columns.
			if (this.leftColumns != 0) {
				alert('Unattached left columns');
				this.leftColumns = 0;
			}
			this.styleMode = styleModeTypes.NONE;
		} else if (tok == '<title>') {
			this.title = '';
			this.styleMode = styleModeTypes.TITLE;
		} else if (tok == '</title>') {
			this.styleMode = styleModeTypes.NONE;
		} else if (tok == '<context>') {
			this.context = '';
			this.styleMode = styleModeTypes.CONTEXT;
		} else if (tok == '</context>') {
			this.styleMode = styleModeTypes.NONE;
		} else if (tok == '<summary>') {
			this.summary = '';
			this.styleMode = styleModeTypes.SUMMARY;
		} else if (tok == '</summary>') {
			this.styleMode = styleModeTypes.NONE;
		} else if (tok == '<suggest>') {
			this.suggest = [];
			this.styleMode = styleModeTypes.SUGGEST;
		} else if (tok == '</suggest>') {
			this.styleMode = styleModeTypes.NONE;
		} else if (tok == '<axiom>') {
			this.isAxiom = true;
		} else if (this.styleMode == styleModeTypes.TABLE) {
			this.read_column_style(tok);
		} else if (this.styleMode == styleModeTypes.TITLE) {
			this.title += tok + ' ';
		} else if (this.styleMode == styleModeTypes.CONTEXT) {
			this.context += tok + ' ';
		} else if (this.styleMode == styleModeTypes.SUMMARY) {
			this.summary += tok + ' ';
		} else if ((this.styleMode == styleModeTypes.SUGGEST) ||
		           (this.styleMode == styleModeTypes.SUGGEST_FUNC)) {
			this.addSuggestToken(tok);
		}
	}
};

GH.Scanner.prototype.get_tok = function() {
    while (this.tokix >= this.toks.length) {
        if (this.lineno == this.lines.length) {
            return null;
        }
        var line = this.lines[this.lineno];
        this.lineno++;
        line = line.replace(/\(|\)/g, ' $& ');
		this.styleScanner.read_styling(line);
        line = line.split('#')[0];
        this.toks = line.split(/[ \t]+/);
        this.tokix = this.toks[0] == '' ? 1 : 0;
        if (this.toks[this.toks.length - 1] == '') {
            this.toks.pop();
        }
    }
    var result = this.toks[this.tokix];
    this.tokix++;
    return result;
};

GH.tableExpression = function(parent, expression, leftColumns, color) {
	this.parent = parent;
	this.expression = expression;
	this.color = color;
	this.rightColumns = '';
	this.leftColumns = '';
	for (var i = 0; i < leftColumns; i++) {
		this.leftColumns += '</td><td>';
	}
	this.children = [];
};

GH.tableExpression.prototype.addExpression = function(tok, leftColumns, color) {
	if (this.expression == null) {
		this.expression = tok;
	} else {
		this.children.push(new GH.tableExpression(this, tok, leftColumns, color));
	}
};

GH.tableExpression.prototype.addRightColumn = function() {
	this.children[this.children.length - 1].rightColumns += '</td><td>';
};

GH.tableExpression.prototype.output = function() {
	var result;
	if (this.children.length > 0) {
		var result = [this.expression];
		for (var i = 0; i < this.children.length; i++) {
			result.push(this.children[i].output());
		}
	} else {
		result = this.expression;
	}

	if (this.color != '') {
		result = ['htmlSpan', this.color, result];
	}
	if ((this.leftColumns != '') || (this.rightColumns != '')) {
		result = ['table', this.leftColumns, result, this.rightColumns];
	}
	return result;
};

GH.read_sexp = function(scanner) {
	scanner.table = null;
    while (1) {
        var tok = scanner.get_tok();
        if (tok == null) {
            return null;
        }
        if (tok == "(") {
            var result = [];
            while (1) {
                var subsexp = GH.read_sexp(scanner);
                if (subsexp == ")") {
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
    if (GH.typeOf(sexp) == 'string') {
        return sexp;
    } else if (GH.typeOf(sexp) == 'number') {
        return '' + sexp; // DLK adding for debug purposes
    } else if (sexp == null) {
        return '#null';  // DLK adding for debug purposes
    } else {
        // map would of course be shorter, but how available is it?
        var result = [];
        for (var i = 0; i < sexp.length; i++) {
            result.push(GH.sexp_to_string(sexp[i]));
        }
        return "(" + result.join(' ') + ")";
    }
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
    if (GH.typeOf(a) == 'undefined') {
      throw 'whoa!';
    }
    if (GH.typeOf(a) == 'string') {
       return a.toString() == b.toString();
    }
    if (GH.typeOf(b) == 'string' || a.length != b.length) {
       return false;
    }
    for (var i = 0; i < a.length; i++) {
        if (!GH.sexp_equals(a[i], b[i])) {
            return false;
        }
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

// Check syntax for a term with result kind 'tkind', signature 'tsig',
// and (optionally) freespec list 'freespecs', in an environment with
// the specified kinds, terms, and syms.
// Return the (kind, argkinds, freemap) tuple.
GH.term_common = function(tkind, tsig, freespecs,  kinds, terms, syms) {
    if (GH.typeOf(tkind) != 'string' || !kinds.hasOwnProperty(tkind)) {
        throw 'Term result kind must be a known kind';
    }
    if (GH.typeOf(tsig) == 'string' || tsig.length < 1 ||
        GH.typeOf(tsig[0]) != 'string') {
        throw 'Term signature must be a list starting with term symbol';
    }
    if (terms.hasOwnProperty(tsig[0])) {
        throw 'A term of name ' + tsig[0] + ' already exists.';
    }
    var argkinds = [];
    var inverse = {};
    var freemap = [];
    for (var i = 0; i < tsig.length - 1; i++) {
        var arg = tsig[i + 1];
        if (GH.typeOf(arg) != 'string' || !syms.hasOwnProperty(arg)) {
            throw ('Term formal argument ' + GH.sexp_to_string(arg) +
                   ' is not a known variable');
        }
        if (inverse.hasOwnProperty(arg)) {
            throw 'Repeated term formal argument ' + arg;
        }
        var vv = syms[arg];
        argkinds.push(vv[1]);
        if (vv[0] == 'tvar') {
            freemap.push(null);
        } else if (vv[0] == 'var') {
            freemap.push([]);
        } else {
            throw 'Symbol ' + arg + ' is not a variable.';
        }
        inverse[arg] = i;
    }
    var k = kinds[tkind];
    if (freespecs == null) {
        return [k, argkinds, freemap];
    }
    if (GH.typeOf(freespecs) == 'string') {
        throw 'A term free variable map must be a list';
    }
    for (i = 0; i < freespecs.length; i++) {
        var clause = freespecs[i];
        if (GH.typeOf(clause) == 'string' || clause.length < 2 ||
            GH.typeOf(clause[0]) != 'string') {
            throw 'Each free variable map clause must be a list of at least two term argument variables';
        }
        var bvar = clause[0];
        var fm = freemap[inverse[bvar]];
        if (!inverse.hasOwnProperty(bvar) || fm == null) {
            throw 'The first variable in a term free variable map clause must be a binding variable argument of the term';
        }
        if (fm.length != 0) {
            throw 'More than one free variable map clause for binding variable ' + bvar;
        }
        for (var j = 1; j < clause.length; j++) {
            var v = clause[j];
            if (GH.typeOf(v) != 'string' || !inverse.hasOwnProperty(v)) {
              throw 'Free variable map clause element is not a term formal argument: ' + GH.sexp_to_string(v);
            }
            var n = inverse[v];
            // is there a method for this?
            if (fm.indexOf(n) >= 0) {
                throw 'Free variable map clause contains ' + v + ' more than once.';
            }
            fm.push(n);
        }
        fm.sort();
    }
    return [k, argkinds, freemap];
};

GH.ProofCtx = function() {
    this.stack = [];
	this.stackHistory = [];
	this.hierarchy = new GH.ProofHierarchy(null, 0, '');
    this.mandstack = [];
    this.defterm = null;
};

GH.VerifyCtx = function(urlctx, run) {
    this.kinds = {};
    this.terms = {};
    this.syms = {};
    this.interfaces = {};
    this.urlctx = urlctx;
    this.run = run;
    this.suppress_errors = false;
	this.error_step = null;
};

GH.VerifyCtx.prototype.set_suppress_errors = function(flag) {
    this.suppress_errors = flag;
};

GH.VerifyCtx.prototype.add_sym = function(label, val) {
    if (this.syms.hasOwnProperty(label)) {
        throw 'Symbol ' + label + ' already defined';
    }
    this.syms[label] = val;
};

GH.VerifyCtx.prototype.add_kind = function(kind, val) {
    if (this.kinds.hasOwnProperty(kind)) {
        throw 'Kind ' + kind + ' already defined';
    }
    this.kinds[kind] = val;
};

GH.VerifyCtx.prototype.get_kind = function(kind) {
    if (this.kinds.hasOwnProperty(kind)) {
        return this.kinds[kind];
    } else {
        throw 'Kind not known: ' + kind;
    }
};

GH.VerifyCtx.prototype.add_term = function(label, term) {
    if (this.terms.hasOwnProperty(label)) {
        throw 'Term ' + label + ' already defined';
    }
    this.terms[label] = term;
};

GH.VerifyCtx.prototype.add_assertion = function(kw, label, fv, hyps, concl,
                varlist, num_hypvars, num_nondummies, syms, styling) {
    var mand = varlist.slice(num_hypvars, num_nondummies);
    // TODO -- probably want to save all of varlist, as well as num_hypvars,
    // num_nondummies
    this.add_sym(label, [kw, fv, hyps, concl, mand, syms, styling]);
};

GH.VerifyCtx.prototype.allvars = function(exp) {
    var fv = [];
    function allvars_rec(exp) {
        if (GH.typeOf(exp) == 'string') {
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

GH.VerifyCtx.prototype.free_scan = function(v, term, accum) {
    if (GH.typeOf(term) == 'string') {
        return accum(term);
    } else {
        var freemap = this.terms[term[0]][2];
        var subterms = term.slice(1);
        var i;
        for (i = 0; i < freemap.length; i++) {
            var fl = freemap[i]; // note fl is sorted if not null
            if (fl == null || term[i + 1] != v) {
                continue;
            }
            for (var j = 0; j < subterms.length; j++) {
                if (fl.indexOf(j) < 0) {
                    subterms[j] = null;
                }
            }
        }
        for (i = 0; i < subterms.length; i++) {
            if (subterms[i] != null &&
                this.free_scan(v, subterms[i], accum)) {
                return true;
            }
        }
        return false;
    }
};

GH.VerifyCtx.prototype.free_in = function(v, term, fvvars) {
    var syms = this.syms;
    function test(vv) {
        if (vv == v) {
            return true;
        }
        if (fvvars == null || syms[vv][0] == 'var') {
            return false;
        }
        return !fvvars.hasOwnProperty(vv);
    }
    return this.free_scan(v, term, test);
};

// Find the set of all variables X occurring in exp, for which
// if binding variable v occurs free in X, v occurs free in exp.
// Add such variables to varset.
// (term is known to be well-formed when this routine is called.)
GH.VerifyCtx.prototype.freeset = function(v, exp, varset) {
    var syms = this.syms;
    function test(vv) {
        if (vv == v || syms[vv][0] != 'var') {
            varset[vv] = 0;
        }
        return false;
    }
    return this.free_scan(v, exp, test);
};

GH.VerifyCtx.prototype.check_free_in = function(v, exp, varset) {
    var syms = this.syms;
    function test(vv) {
        if (vv.valueOf() == v.valueOf()) {
            return true; // only return true if vv explicitly free
        }
        if (varset == null || syms[vv][0] == 'var') {
            return false;
        }
        if (!varset.hasOwnProperty(vv)) {
            varset[vv] = null;
            return false;
        }
        if (varset[vv] == 0) {
            varset[vv] = 1;
        }
        return false;
    }
    return this.free_scan(v, exp, test);
};



// Check well-formedness of exp, and return its kind. Add variables
// encountered while scanning exp to array varlist and object varmap
// if they are not already present.  varlist records the variable
// sort/kind/name tuples in order, and varmap maps variable names to 
// their indices in varlist.
// The syms object is a dictionary in which we look up variable names
// to find their sort/kind information.
GH.VerifyCtx.prototype.kind_of = function(exp, varlist, varmap,
                                          binding_var, syms) {
    var v;
    if (GH.typeOf(exp) == 'string') {
        v = syms[exp];
        if (!syms.hasOwnProperty(exp) ||
            (v[0] != 'var' && v[0] != 'tvar')) {
            throw exp + ' is not a defined variable.';
        }
        if (binding_var && v[0] != 'var') {
            throw 'Expected a binding variable but found ' + exp;
        }
        if (!varmap.hasOwnProperty(exp)) {
            varmap[exp] = varlist.length;
            varlist.push(v);
        }
        return this.kinds[v[1]];
    }
    if (exp.length == 0) {
      throw "Term can't be empty.";
    }
    if (GH.typeOf(exp[0]) != 'string') {
      throw 'Term symbol must be id';
    }
    if (!this.terms.hasOwnProperty(exp[0])) {
        if (syms.hasOwnProperty(exp[0])) {
	        throw exp[0] + ' is a variable not a operator. Operators always come before variables.';
		} else {
	        throw 'Term ' + exp[0] + ' not known';
		}
    }
    if (binding_var) {
        throw ('Expected a binding variable but found ' +
               GH.sexp_to_string(exp));
    }
    v = this.terms[exp[0]];
    if (exp.length - 1 != v[1].length) {
        throw (GH.VerifyCtx.arityMessage(exp[0], v[1].length, (exp.length - 1)));
    }
    for (var i = 0; i < exp.length - 1; i++) {
        binding_var = v[2][i] != null;
        var child_kind = this.kind_of(exp[i + 1], varlist, varmap, 
                                      binding_var, syms);
        if (child_kind != this.kinds[v[1][i]]) {
            throw 'Kind mismatch. Expected ' + this.kinds[v[1][i]] + ', but got a ' + child_kind + ': ' + exp[i + 1] + '.';
        }
    }
    return this.kinds[v[0]];
};

GH.VerifyCtx.arityMessage = function(name, expected, actual) {
	var result = name + ' is a ';
	switch (expected) {
		case 0: result += 'constant';					break;
		case 1: result += 'unary operation';			break;
		case 2: result += 'binary operation';			break;
		case 3: result += 'ternary operation';			break;
		default: result += expected + '-ary operation';	break;
	}
	if ((name == '-n') && (actual == 2)) {
		return 'Negative ' + result + ". For binary subtraction use '-'.";
	} else if ((name == '-') && (actual == 1)) {
		return 'Subtraction ' + result + ". For the unary negative sign use '-n.'";
	}
	result += '. Expected ' + expected + ' arguments, got ' + actual + '.';
	return result;
};

GH.VerifyCtx.prototype.get_import_ctx = function(prefix, pifs) {
    return new GH.ImportCtx(this, prefix, pifs);
};
GH.VerifyCtx.prototype.get_export_ctx = function(prefix, pifs) {
    return new GH.ExportCtx(this, prefix, pifs);
};

GH.VerifyCtx.prototype.do_cmd = function(cmd, arg, styling) {
  var i, j, label, fv, hyps, concl, proof, new_hyps, proofctx;
    if (cmd == 'thm') {
        if (arg.length < 5) {
            throw 'Expected at least 5 args to thm';
        }
        label = arg[0];
        fv = arg[1];
        hyps = arg[2];
        concl = arg[3];
        proof = arg.slice(4);
        log('checking ' + label);
        proofctx = new GH.ProofCtx();
        this.check_proof(proofctx, label, fv, hyps, concl, proof, null, null);
        if (!this.suppress_errors && !GH.sexp_equals(proofctx.stack[0], concl)) {
            throw ('Stack has:\n ' + GH.sexp_to_string(proofctx.stack[0]) +
                   '\nWanted:\n ' + GH.sexp_to_string(concl));
        }
        new_hyps = [];
        for (j = 1; j < hyps.length; j += 2) {
            new_hyps.push(hyps[j]);
        }
        // Hmm, could possibly save proofctx.varmap instead of this.syms...
        // If we go to index variable expression storage we don't need either
        this.add_assertion('thm', label, fv, new_hyps, concl,
                           proofctx.varlist, proofctx.num_hypvars,
                           proofctx.num_nondummies, this.syms, styling);
        return;
    }
    if (cmd == 'defthm') {
        if (arg.length < 7) {
            throw 'Expected at least 7 args to thm';
        }
        label = arg[0];
        var dkind = arg[1];
        var dsig = arg[2];
        fv = arg[3];
        hyps = arg[4];
        concl = arg[5];
        proof = arg.slice(6);
        log('checking defthm ' + label);
        proofctx = new GH.ProofCtx();
        this.check_proof(proofctx, label, fv, hyps, concl, proof,
                         dkind, dsig);
        proofctx.definiens = null;
        this.def_conc_match(concl, proofctx.stack[0], proofctx, dsig);
        if (proofctx.definiens == null) {
            throw 'Term being defined does not occur in conclusion.';
        }
        log ('  ' + GH.sexp_to_string(dsig) + '  ' +
             GH.sexp_to_string(proofctx.definiens) + '  ' +
             GH.sexp_to_string(proofctx.defterm[2]));
        new_hyps = [];
        for (j = 1; j < hyps.length; j += 2) {
            new_hyps.push(hyps[j]);
        }
        this.terms[dsig[0]] = proofctx.defterm;
        this.add_assertion('thm', label, fv, new_hyps, concl,
                           proofctx.varlist, proofctx.num_hypvars,
                           proofctx.num_nondummies, this.syms, styling);
        return;
    }
    if (cmd == 'import' || cmd == 'export') {
        if (GH.typeOf(arg) == 'string' || arg.length != 4 ||
            GH.typeOf(arg[0]) != 'string' || GH.typeOf(arg[1]) != 'string' ||
            GH.typeOf(arg[2]) == 'string' || GH.typeOf(arg[3]) != 'string') {
            throw ("Expected '" + cmd +
                   " (IFNAME URL (IFNAME ...) \"PREFIX\")'");
        }
        var iname = arg[0];
        var url = arg[1];
        var params = arg[2];
        var prefix = arg[3];
        if (prefix.length < 2 || prefix.charAt(0) != '"' || prefix.charAt(prefix.length - 1) != '"') {
            throw 'Namespace prefix must be enclosed in quotes';
        }
        prefix = prefix.substring(1, prefix.length - 1);
        if (this.interfaces.hasOwnProperty(iname)) {
            throw "An interface of name '" + iname + "' already exists.";
        }
        var pifs = [];
        var inverse = {};
        for (i = 0; i < params.length; i++) {
            var p = params[i];
            if (GH.typeOf(p) != 'string') {
                throw cmd + ' parameter must be an interface name';
            }
            if (!this.interfaces.hasOwnProperty(p)) {
                throw 'Unknown interface ' + p;
            }
            if (inverse.hasOwnProperty(p)) {
                throw 'Interface parameter ' + p + ' was repeated.';
            }
            inverse[p] = 0;
            var iface = this.interfaces[p];
            pifs.push(iface);
        }
        var ctx;
        if (cmd == 'import') {
            log ('Importing ' + iname);
            ctx = this.get_import_ctx(prefix, pifs);
        } else {
            log ('Exporting ' + iname);
            ctx = this.get_export_ctx(prefix, pifs);
        }
        this.run(this.urlctx, url, ctx);
        if (ctx.n_used_params != pifs.length) {
            throw ('Not all parameters passed to ' + cmd +
                   ' interface ' + iname + ' were used.');
        }
        delete ctx.terms; // only keep myterms
        delete ctx.kinds; // only keep mykinds
        this.interfaces[iname] = ctx;
        return;
    }
    if (cmd == 'var' || cmd == 'tvar') {
        if (GH.typeOf(arg) == 'string' || arg.length < 1) {
            throw "Expected '" + cmd + " (KIND VAR ...)'";
        }
        var kind = this.get_kind(arg[0]);
        for (i = 1; i < arg.length; i++) {
            if (GH.typeOf(arg[i]) != 'string') {
                throw 'variable name must be an identifier.';
            }
            this.add_sym(arg[i], [cmd, kind, arg[i]]);
        }
        return;
    }
    if (cmd == 'kindbind') {
        if (GH.typeOf(arg) == 'string' || arg.length != 2 ||
            GH.typeOf(arg[0]) != 'string' || GH.typeOf(arg[1]) != 'string') {
            throw "Expected 'kindbind (OLDKIND NEWKIND)'";
        }
        this.add_kind(arg[1], this.get_kind(arg[0]));
        return;
    }
    if (cmd == 'term' || cmd == 'param' || cmd == 'kind') {
		return;
        throw 'Interface file command encountered in proof file.';
    }
    throw 'Unrecognized command ' + cmd;
};

// Check that the defthm conclusion <conc> properly matches the
// remnant expression <remnant> on the proof stack.
// <concl> and <remnant> are known to be well-formed at this point.
GH.VerifyCtx.prototype.def_conc_match = function(concl, remnant, 
                                                 proofctx, dsig) {
    if (GH.typeOf(concl) == 'string') {
        if (concl != remnant) {
            throw ('defthm conclusion mismatch: ' + concl + '\nversus: ' +
                   GH.sexp_to_string(remnant));
        }
        return;
    }
    if (GH.typeOf(remnant) == 'string') {
        throw ('defthm conclusion mismatch: expected term, found\n ' +
               remnant);
    }
    var i;
    if (concl[0] == remnant[0]) {
        // since concl and remnant are well-formed, they both have the same
        // length.
        for (i = 1; i < concl.length; i++) {
            this.def_conc_match(concl[i], remnant[i], proofctx, dsig);
        }
        return;
    }
    if (concl[0] != dsig[0]) {
        throw ('defthm conclusion mismatch: expected\n ' +
               GH.sexp_to_string(concl) + '\nbut found\n ' +
               GH.sexp_to_string(remnant));
    }
    for (i = 1; i < concl.length; i++) {
        if (concl[i] != dsig[i]) {
            throw ('All uses of the term being defined in the defthm conclusion must exactly match the definition term signature');
        }
    }
    if (proofctx.definiens != null) {
        if (!GH.sexp_equals(proofctx.definiens, remnant)) {
            throw 'All remnant subexpressions matching the definition term in the defthm conclusion must be identical.';
        }
        return;
    }
    // OK, this is the first time we've seen the definiens, i.e. the
    // subexpression of the remnant that matches occurrences of the
    // definition term in the conclusion. Need to check that:
    // - all formal arguments of the definition term occur in remnant
    // - For any variable v occurring in remnant that isn't one of the formal
    //   arguments, all of the following hold:
    //   - v is a proof dummy variable (doesn't occur in hypotheses or
    //     conclusion
    //   - v is a binding variable
    //   - v does not occur free in the remnant.

    var remvars = this.allvars(remnant); // ugh.
    var argcount = 0;
    for (i = 0; i < remvars.length; i++) {
        var v = remvars[i];
        var vix = proofctx.varmap[v];  // will be found
        if (vix < proofctx.num_nondummies) {
            if (concl.indexOf(v, 1) >= 0) {
                argcount++;  // keep track of how many arg vars we've seen
            } else {
                throw 'Definition dummy variable ' + v + ' is not a proof dummy variable';
            }
            continue;
        }
        // v is a definition dummy and a proof dummy.
        if (proofctx.varlist[vix][0] != 'var') {
            throw 'Definition dummy variable ' + v + ' is not a binding variable';
        }
        if (this.free_in(v, remnant, null)) {
            throw ('Definition dummy variable ' + v + ' occurs free in ' +
                   GH.sexp_to_string(remnant));
        }
    }
    if (argcount != dsig.length - 1) {
        throw 'Not all formal definition arguments occurred in definiens.';
    }
    // construct the freemap
    var freemap = proofctx.defterm[2];
    for (i = 0; i < freemap.length; i++) {
        var fm = freemap[i];
        if (fm == null) {
            continue;
        }
        var l = {};
        this.freeset(concl[i + 1], remnant, l);
        for (var j = 0; j < freemap.length; j++) {
            if (l.hasOwnProperty(concl[j + 1])) {
                fm.push(j);
            }
        }
    }
    proofctx.definiens = remnant;
};

GH.VerifyCtx.prototype.fvmap_build = function(fv, varlist, varmap) {
    var num_nondummies = varlist.length;
    var fvmap = {};
    var v, i, j;
    for (i = 0; i < num_nondummies; i++) {
        v = varlist[i];
        if (v[0] == 'var') {
            fvmap[v[2]] = {};  // note, only nondummies get fvmap entries
        }
    }
    for (i = 0; i < fv.length; i++) {
        var clause = fv[i];
        if (GH.typeOf(clause) == 'string' || clause.length == 0) {
            throw 'Each fv clause must be list of vars';
        }
        var tvar = clause[0];
        if (GH.typeOf(tvar) != 'string') {
            throw 'Var in fv clause must be string';
        }
        if (!(varmap.hasOwnProperty(tvar) && 
              varlist[varmap[tvar]][0] == 'tvar')) {
            throw 'First var in fv clause must be nondummy tvar: ' + tvar;
        }
        for (j = 1; j < clause.length; j++) {
            v = clause[j];
            if (GH.typeOf(v) != 'string') {
                throw 'Var in fv clause must be string';
            }
            // Check that v is a binding variable occurring in the 
            // hypotheses or conclusion.
            if (!fvmap.hasOwnProperty(v)) {
                throw 'Spurious (or non-binding) variable in fv list: ' + v;
            }
            fvmap[v][tvar] = 0;
        }
    }
    return fvmap;
};

GH.VerifyCtx.prototype.check_proof = function(proofctx,
                                              label, fv, hyps, stmt, proof,
                                              dkind, dsig) {
    var defterm;
    if (dkind == null) {
        if (GH.typeOf(label) != 'string' || GH.typeOf(fv) == 'string' ||
            GH.typeOf(hyps) == 'string') {
            throw "Expected 'thm (LABEL ((TVAR BVAR BVAR ...)) ({HYPNAME HYP} ...) CONCL STEP STEP ...)'";
        }
    } else {
        if (GH.typeOf(label) != 'string' || GH.typeOf(dkind) != 'string' ||
            GH.typeOf(dsig) == 'string' || GH.typeOf(fv) == 'string' ||
            GH.typeOf(hyps) == 'string') {
            throw "Expected 'defthm (LABEL KIND (TNAME VAR ...) ((TVAR BVAR BVAR ...)) ({HYPNAME HYP} ...) CONCL STEP STEP ...)'";
        }
        defterm = GH.term_common(dkind, dsig, null, 
                                 this.kinds, this.terms, this.syms);
    }
    if (hyps.length & 1) {
        throw 'hypothesis list must be of even length';
    }
    var varlist = [];
    var varmap = {};
    var i;
    var hypmap = {};
    for (i = 0; i < hyps.length; i += 2) {
        if (GH.typeOf(hyps[i]) != 'string') {
            throw 'Hyp label must be string';
        }
        if (hypmap.hasOwnProperty(hyps[i])) {
            throw 'Repeated hypothesis label ' + hyps[i];
        }
        hypmap[hyps[i]] = hyps[i + 1];
        this.kind_of(hyps[i + 1], varlist, varmap, false, this.syms);
    }
    var num_hypvars = varlist.length;
    if (dkind != null) {
        var j;
        // Check that the defined term does not have more than one binding variable argument of a given kind.
        var fmap = defterm[2];
        var ak = defterm[1];
        for (j = 1; j < fmap.length; j++) {
            if (fmap[j] == null) {
                continue; // skip term variable formal arguments
            }
            for (i = 0; i < j; i++) {
                if (fmap[i] == null) {
                    continue;
                }
                if (ak[i] == ak[j]) {
                    throw ('Formal binding variable arguments ' + dsig[i+1] +
                           ' and ' + dsig[j+1] + ' of defined term ' + 
                           dsig[0] + ' have the same kind.');
                }
            }
        }
        // temporarily add the new term to this.terms while we parse the
        // conclusion
        this.terms[dsig[0]] = defterm;
    }
    this.kind_of(stmt, varlist, varmap, false, this.syms);
    if (dkind != null) {
        // remove temporarily added term being defined
        delete this.terms[dsig[0]];
    }
    var num_nondummies = varlist.length;

    proofctx.fvvarmap = this.fvmap_build(fv, varlist, varmap);
    proofctx.varlist = varlist;
    proofctx.varmap = varmap;
    proofctx.num_hypvars = num_hypvars;
    proofctx.num_nondummies = num_nondummies;

    if (dkind != null) {
        proofctx.defterm = defterm;
    }
    try {
    for (i = 0; i < proof.length; i++) {
        this.check_proof_step(hypmap, proof[i],  proofctx, null);
    }
    if (proofctx.mandstack.length != 0) {
        throw 'Extra mand hyps on stack at end of proof';
    }
    if (proofctx.stack.length != 1) {
        throw 'Stack must have one term at end of proof';
    }
	var expectedfv = '';
    var missing = '';
    var extra = '';
    var v, nfis, A, val;
    for (v in proofctx.fvvarmap) {
      if (proofctx.fvvarmap.hasOwnProperty(v)) {
        nfis = proofctx.fvvarmap[v];
        for (A in nfis) {
          if (nfis.hasOwnProperty(A)) {
              val = nfis[A];
			  var pair = "(" + A + " " + v + ")";
              if (val == null) {
                  missing = missing + pair;
		          expectedfv = expectedfv + pair;
              } else if (val == 0) {
                  extra = extra + " (" + A + " " + v + ")";
              } else if (val > 0) {
				  expectedfv = expectedfv + pair;
              }
          }
        }
      }
    }
    if (missing != '') {
		expectedfv = '(' + expectedfv + ')';
        throw 'Missing free variable constraint context pairs: ' + missing +
            ' <a onclick="window.direct.replaceText(\'' + expectedfv + '\',' + fv.beg + ',' + fv.end + ')"><b>Fix</b></a>';
    }
    if (extra != '') {
		expectedfv = '(' + expectedfv + ')';
        throw 'Extra free variable constraint context pairs: ' + extra +
            ' <a onclick="window.direct.replaceText(\'' + expectedfv + '\',' + fv.beg + ',' + fv.end + ')"><b>Fix</b></a>';
    }
    } catch (e) {
        if (!this.suppress_errors) {
            throw e;
        }
    }
    return;
};

GH.VerifyCtx.prototype.check_proof_step = function(hypmap, step, proofctx, tagName) {
    var kind;
	this.error_step = null;
    if (GH.typeOf(step) != 'string') {
        kind = this.kind_of(step, proofctx.varlist, proofctx.varmap, false,
                            this.syms);
        proofctx.mandstack.push([['tvar', kind], step]);
        return;
    } 
    if (hypmap.hasOwnProperty(step)) {
        if (proofctx.mandstack.length != 0) {
            throw 'Hyp expected no mand hyps, got ' + proofctx.mandstack.length;
        }
		var hyp = hypmap[step];
		proofctx.stack.push(hyp);
		var styling = tagName ? new GH.styling(null, tagName, '', '', 0, false) : null;
		var proofStep = new GH.ProofStep(step, [], hyp, step.beg, step.end, proofctx.mandstack, false, styling);
		proofctx.stackHistory.push(proofStep);
		var hierarchy = proofctx.hierarchy;
		hierarchy.appendChild(new GH.ProofHierarchy(proofStep, proofStep.begin, ''));
		return;
    }
    if (!this.syms.hasOwnProperty(step)) {
        throw step + " - Unknown Step";
    }
    var v = this.syms[step];
    if (v[0] == 'var' || v[0] == 'tvar') {
        if (!proofctx.varmap.hasOwnProperty(step)) {
            proofctx.varmap[step] = proofctx.varlist.length;
            proofctx.varlist.push(v);
        }
        proofctx.mandstack.push([v, step]);
        return;
    } 
    // This test is now likely redundant...
	if (v[0] == 'stmt' || v[0] == 'thm') {
		var result = this.match_inference(v, proofctx, proofctx.mandstack);
		var sp = proofctx.stack.length - v[2].length;
		proofctx.stack.splice(sp);
		proofctx.stack.push(result);

		var removed = proofctx.stackHistory.splice(sp);
		var styling = v[6] ? v[6] : new GH.styling(null, null, '', '', 0, false);
		var proofStep = new GH.ProofStep(step, removed, result, step.beg, step.end, proofctx.mandstack, false, styling);
		proofctx.stackHistory.push(proofStep);
		var hierarchy = proofctx.hierarchy;		
		hierarchy.appendChild(new GH.ProofHierarchy(proofStep, proofStep.begin, ''));
		var reparented = false;
		for (var i = 0; i < removed.length; i++) {
			if (removed[i].hierarchy.parent == proofStep.hierarchy.parent) {
				removed[i].hierarchy.reparent(proofStep.hierarchy);
				reparented = true;
			}
		}
		if (reparented) {
			// Remove the step we just added and add it as a child instead.
			var newHierarchy = new GH.ProofHierarchy(proofStep, proofStep.begin, '');
			var lastChild = hierarchy.children[hierarchy.children.length - 1];
			lastChild.appendChild(newHierarchy);
			lastChild.step = null;
		}
		proofctx.mandstack = [];
    }
};

GH.VerifyCtx.prototype.match_inference = function(v, proofctx, mandstack) {
        var fv = v[1];
        var hyps = v[2];
        var concl = v[3];
        var mand = v[4];
        var syms = v[5];
        if (mand.length != mandstack.length) {
			this.error_step = v;
            throw 'Expected ' + mand.length + ' mand hyps, got ' + mandstack.length;
        }
        var env = {};
        var el;
        for (var i = 0; i < mand.length; i++) {
            var mv = mand[i];
            el = mandstack[i];
            if (el[0][1] != mv[1]) {
				this.error_step = v;
                throw ('Kind mismatch for ' + mv[2] + ': expected ' +
                       mv[1] + ' but found ' + el[0][2] + ' which is a ' + el[0][1]);
            }
            if (mv[0] == 'var' && el[0][0] != 'var') {
				this.error_step = v;
                throw ('Unifying, expected expression substituted for mandatory variable ' +
                       mv[2] + ' to be a binding variable, but found ' +
                       GH.sexp_to_string(el[1]));
            }
            this.match(mv[2], el[1], env);
        }
        var sp = proofctx.stack.length - hyps.length;
        if (sp < 0) {
            throw 'Stack underflow';
        }
        for (i = 0; i < hyps.length; i++) {
            el = proofctx.stack[sp + i];
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
          if (env.hasOwnProperty(v)) {
            var exp = env[v];
            if (syms[v][0] == 'var') {
                if (GH.typeOf(exp) != 'string') {
                    throw 'Expected binding variable for ' + v;
                }
                if (this.syms[exp][0] != 'var') {
                    throw 'Expected binding variable for ' + v + '; ' + exp + ' is term variable';
                }
                if (invmap.hasOwnProperty(exp)) {
                    throw 'Binding variables ' + invmap[exp] + ' and ' + v + ' both map to ' + exp;
                }
                invmap[exp] = v;
            }
          }
        }
        var result = this.apply_subst(concl, env);
        return result;
};

GH.VerifyCtx.prototype.free_in_proof = function(v, term, proofctx) {
    return this.check_free_in(v, term, proofctx.fvvarmap[v] || null);
};

/**
 * Attempts to fit the expression exp into the template templ, in
 * accordance with existing assignments stored in env (a map of vars
 * to terms).  On failure, throws up.
 */
GH.VerifyCtx.prototype.match = function(templ, exp, env, alreadyExpanded) {
    if (0) {
        log('match: templ=' + GH.sexp_to_string(templ) + '  exp=' + GH.sexp_to_string(exp)
            + (alreadyExpanded ? " aE" : ""));
    }
    function UnificationError(mesg, found, expected) {
        this.toString = function() {
            return "Unification error: " + mesg
                + " expected " + GH.sexptohtml(expected, false)
                + " got " + GH.sexptohtml(found, false)
                + (found.beg ? "[" + found.beg + ":" + found.end + "]" : "");
        };
        if (found.beg) {
            this.expected = GH.sexp_to_string(expected);
            this.found = GH.sexp_to_string(found);
        } else {
            this.found = GH.sexp_to_string(expected);
            this.expected = GH.sexp_to_string(found);
        }
    }
    if (GH.typeOf(templ) == 'string') {
        if (alreadyExpanded) {
            if (templ.toString() != exp) {
                throw new UnificationError("1", exp, templ);
            }
        } else {
            if (env.hasOwnProperty(templ)) {
                this.match(env[templ], exp, env, true);
            } else {
                env[templ] = exp;
            }
        }
    } else {
        if (GH.typeOf(exp) == 'string') {
            throw new UnificationError("2", exp, templ);
        }
        if (templ[0].toString() != exp[0]) {
            throw new UnificationError("3", exp, templ);
        }
        if (exp.length != templ.length) {
            throw new UnificationError("Length mismatch", exp, templ);
        }
        for (var i = 1; i < templ.length; i++) {
            this.match(templ[i], exp[i], env, alreadyExpanded);
        }
    }
};

GH.VerifyCtx.prototype.apply_subst = function(templ, env) {
    if (GH.typeOf(templ) == 'string') {
        return env[templ];
    } else {
        var result = [templ[0]];
        for (var i = 1; i < templ.length; i++) {
            result.push(this.apply_subst(templ[i], env));
        }
        return result;
    }
};

GH.InterfaceCtx = function(verify, prefix, params) {
    this.verify = verify;
    this.prefix = prefix;
    this.params = params;
    this.vars = {};
    this.mykinds = {};
    this.kinds = {};
    this.myterms = {};
    this.terms = {};
    this.used_params = {};
    this.n_used_params = 0;
};

GH.InterfaceCtx.prototype.get_kind = function(rawkind) {
    return this.verify.get_kind(this.kinds[rawkind]);
};

GH.InterfaceCtx.prototype.var_cmd = function(cmd, arg) {
    if (GH.typeOf(arg) == 'string' || arg.length < 1 || 
        GH.typeOf(arg[0]) != 'string') {
        throw "Expected '" + cmd + " (KIND NAME ...)'";
    }
    var kind = this.get_kind(arg[0]);
    for (var i = 1; i < arg.length; i++) {
        var v = arg[i];
        if (GH.typeOf(v) != "string") {
            throw 'variable name must be an atom';
        }
        if (this.vars.hasOwnProperty(v)) {
            throw 'Variable ' + v + ' already defined';
        }
        this.vars[v] = [cmd, kind, arg[i]];
    }
};

GH.InterfaceCtx.prototype.param_cmd = function(arg) {
    if (GH.typeOf(arg) == 'string' || arg.length != 4 ||
        GH.typeOf(arg[0]) != 'string' || GH.typeOf(arg[1]) != 'string' ||
        GH.typeOf(arg[2]) == 'string' || GH.typeOf(arg[3]) != 'string') {
        throw "Expected 'param (IFNAME URL (IFNAME ...) \"PREFIX\")'";
    }
    var ifname = arg[0];
    // var url = arg[1];
    var params = arg[2];
    var prefix = arg[3];
    if (prefix.length < 2 || prefix.charAt(0) != '"' ||
        prefix.charAt(prefix.length - 1) != '"') {
        throw 'param prefix must be enclosed in quotes';
    }
    prefix = prefix.substring(1, prefix.length - 1);
    if (this.used_params.hasOwnProperty(ifname)) {
        throw "The interface '" + ifname + "' has already been used.";
    }
    var n = this.n_used_params;
    if (n >= this.params.length) {
        throw "More param commands than provided parameter interfaces";
    }
    var iface = this.params[n];
    if (iface.params.length != params.length) {
        throw ("param interface '" + ifname + "' requires " + 
               params.length + " parameters.");
    }
    var i;
    for (i = 0; i < params.length; i++) {
        var p = params[i];
        if (GH.typeOf(p) != 'string') {
            throw 'Parameters to param must be interface names.';
        }
        if (!this.used_params.hasOwnProperty(p)) {
            throw 'Unknown interface name ' + p;
        }
        var pif = this.used_params[p];
        if (pif != iface.params[i]) {
            throw 'Inconsistent parametrization of interface ' + ifname;
        }
    }
    // Add kinds and terms from the parameter interface to import context
    // Check for duplicates arising from prefix differences
    var v;
    for (v in iface.mykinds) {
      if (iface.mykinds.hasOwnProperty(v)) {
        var kpref = prefix + v;
        if (this.kinds.hasOwnProperty(kpref)) {
            throw 'A kind ' + kpref + ' already exists in import context.';
        }
        this.kinds[kpref] = iface.mykinds[v];
      }
    }
    for (v in iface.myterms) {
      if (iface.myterms.hasOwnProperty(v)) {
        var tpref = prefix + v;
        if (this.kinds.hasOwnProperty(tpref)) {
            throw ('A term symbol ' + tpref +
                   ' already exists in import context.');
        }
        this.terms[tpref] = iface.myterms[v];
      }
    }
    this.used_params[ifname] = iface;
    this.n_used_params = n + 1;
};

GH.InterfaceCtx.prototype.kind_cmd_common = function(arg) {
    if (GH.typeOf(arg) == 'string' || arg.length != 1) {
        throw 'Kind takes one arg';
    }
    if (GH.typeOf(arg[0]) != 'string') {
        throw 'Kind must be string';
    }
    var loc_kind = arg[0];
    if (this.kinds.hasOwnProperty(loc_kind)) {
        throw 'Kind ' + loc_kind + ' already exists in import context.';
    }
    var kind = this.prefix + arg[0];
    this.mykinds[loc_kind] = kind;
    this.kinds[loc_kind] = kind;
    return kind;
};

GH.ImportCtx = function(verify, prefix, params) {
    GH.InterfaceCtx.call(this, verify, prefix, params);
};

GH.ImportCtx.prototype = new GH.InterfaceCtx();

GH.ImportCtx.prototype.map_syms = function(sexp, mapping, varlist,
                                           used_vars, kind, binding_var) {
    // Check well-formedness of expression sexp in import context
    // while translating the expression terms into verify
    // context, and collecting all the variables used in varlist and
    // used_vars.
    if (GH.typeOf(sexp) == 'string') {
        if (!this.vars.hasOwnProperty(sexp)) {
            throw 'Unknown variable ' + sexp;
        }
        var vv = this.vars[sexp];
        if (kind != null && vv[1] != kind) {
            throw 'Expected variable of kind ' + kind + ', found ' + sexp;
        }
        if (binding_var && vv[0] != 'var') {
            throw 'Expected a binding variable, found ' + sexp;
        }
        if (!used_vars.hasOwnProperty(sexp)) {
            used_vars[sexp] = varlist.length;
            varlist.push(vv);
        }
        return sexp;
    } else {
        if (sexp.length < 1) {
            throw '() is not a valid term expression.';
        }
        var locterm = sexp[0];
        if (GH.typeOf(locterm) != 'string') {
            throw 'Bad term symbol' + GH.sexp_to_string(locterm);
        }
        if (!mapping.hasOwnProperty(locterm)) {
            throw 'Unknown term ' + locterm;
        }
        var vterm = mapping[locterm];
        var t = this.verify.terms[vterm];
        if (kind != null && t[0] != kind) {
            throw ('Expected term of kind ' + kind + ', but found ' +
                   GH.sexp_to_string(sexp));
        }
        var result = [vterm];
        var argkinds = t[1];
        var freemap = t[2];
        if (argkinds.length != sexp.length - 1) {
            throw ('Expected ' + argkinds.length + ' arguments for term ' +
                   locterm + ', but found ' + GH.sexp_to_string(sexp));
        }
        for (var i = 1; i < sexp.length; i++) {
            var binding = (freemap[i - 1] != null);
            result.push(this.map_syms(sexp[i], mapping, varlist, used_vars,
                                      argkinds[i - 1], binding));
        }
        return result;
    }
};

GH.ImportCtx.prototype.do_cmd = function(cmd, arg, styling) {
    var kind, i, j, v, vv;
    if (cmd == 'stmt') {
        // import context 'stmt' command
        if (GH.typeOf(arg) == 'string' || arg.length != 4 ||
            GH.typeOf(arg[0]) != 'string' || GH.typeOf(arg[1]) == 'string' ||
            GH.typeOf(arg[2]) == 'string') {
            throw "Expected 'stmt (LABEL ((TVAR BVAR ...) ...) (HYP ...) CONCL)'";
        }
        var local_label = arg[0];
        var fv = arg[1];
        var local_hyps = arg[2];
        var local_concl = arg[3];
        var label = this.prefix + local_label;
        var varlist = [];
        var used_vars = {};
        // log ('terms: ' + JSON.stringify(this.terms))
        var hyps = [];
        for (i = 0; i < local_hyps.length; i++) {
            hyps.push(this.map_syms(local_hyps[i], this.terms, varlist,
                                    used_vars, null, false));
        }
        var num_hypvars = varlist.length;
        var concl = this.map_syms(local_concl, this.terms, varlist,
                                  used_vars, null, false);
        // Check fv.
        for (i = 0; i < fv.length; i++) {
            var clause = fv[i];
            if (GH.typeOf(clause) == 'string' || clause.length < 2) {
                throw 'Each free variable constraint context clause must be a list of at least two variables.';
            }
            var want = 'tvar';
            for (j = 0; j < clause.length; j++) {
                v = clause[j];
                if (GH.typeOf(v) != 'string') {
                    throw 'Free variable constraint clause list elements must be variables';
                }
                if (!this.vars.hasOwnProperty(v)) {
                    throw 'Unknown variable ' + v;
                }
                vv = this.vars[v];
                if (vv[0] != want) {
                    throw 'The first variable in a free variable constraint clause must be a term variable, and the remaining variables must be binding variables.';
                }
                want = 'var';
                if (!used_vars.hasOwnProperty(v)) {
                    throw 'The variable ' + v + ' does not occur in the statement hypotheses or conclusions';
                }
            }
        }
        this.verify.add_assertion('stmt', label, fv, hyps, concl,
                                  varlist, num_hypvars, varlist.length,
                                  this.vars, styling);
        return;
    }
    if (cmd == 'term') {
        // import context 'term' command
        if (GH.typeOf(arg) == 'string' || arg.length < 2) {
            throw "Expected 'term (KIND (NAME ARGVAR ...) (BARGVAR TARGVAR ...) ...'";
        }
        var term = GH.term_common(arg[0], arg[1], arg.slice(2), 
                                  this.kinds, this.terms, this.vars);

        var local_termname = arg[1][0];
        var termname = this.prefix + local_termname;

        this.verify.add_term(termname, term);
        this.terms[local_termname] = termname;
        this.myterms[local_termname] = termname;
        return;
    }
    if (cmd == 'kind') {
        // import context 'kind' command
        kind = this.kind_cmd_common(arg);
        this.verify.add_kind(kind, kind);
        return;
    }
    if (cmd == 'var' || cmd == 'tvar') {
        this.var_cmd(cmd, arg);
        return;
    }
    if (cmd == 'param') {
        this.param_cmd(arg);
        return;
    }
    throw 'Unknown interface command ' + cmd;
};

GH.ExportCtx = function(verify, prefix, params) {
    GH.InterfaceCtx.call(this, verify, prefix, params);
    this.assertions = {};
};

GH.ExportCtx.prototype = new GH.InterfaceCtx();

// Match export-context expression sexp against verify-context
// expression vexp, building variable map varmap from export-context
// variables to verify-context variables as one goes.
// Return true on success, or false on failure.
// Note that this applies both syntactical and proof checks.
// Failures on some syntactic checks throw immediately.
GH.ExportCtx.prototype.export_match = function(exp, vexp, varmap, invmap) {
    if (GH.typeOf(exp) == 'string') {
        if (GH.typeOf(vexp) != 'string') {
            return false;
        }
        if (varmap.hasOwnProperty(exp)) {
            return (varmap[exp] == vexp);
        }
        if (!this.vars.hasOwnProperty(exp)) {
            throw 'Unknown variable' + exp;
        }
        var v = this.vars[exp];
        var vv = this.verify.syms[vexp];
        if (v[0] != vv[0] || v[1] != vv[1]) {
            log ('sort or kind mismatch for ' + exp);
            return false;
        }
        if (invmap.hasOwnProperty(vexp)) {
            log ('Non one-to-one variable mapping');
            return false;
        }
        varmap[exp] = vexp;
        invmap[vexp] = exp;
        return true;
    }
    if (GH.typeOf(vexp) == 'string') {
        return false;
    }
    if (exp.length < 1) {
        throw 'The empty list () is not a valid term expression.';
    }
    if (GH.typeOf(exp[0]) != 'string') {
        throw 'A term expression must start with a term symbol.';
    }
    if (!this.terms.hasOwnProperty(exp[0])) {
        throw 'Unknown term ' + exp[0];
    }
    if (exp.length != vexp.length) {
        return false;
    }
    var prefterm = this.prefix + exp[0];
    if (prefterm != vexp[0]) {
        return false;
    }
    for (var i = 1; i < exp.length; i++) {
        if (!this.export_match(exp[i], vexp[i], varmap, invmap)) {
            return false;
        }
    }
    return true;
};

GH.ExportCtx.prototype.do_cmd = function(cmd, arg, styling) {
    var kind, i, j, v, vv;
    if (cmd == 'stmt') {
        // export context 'stmt' command
        if (GH.typeOf(arg) == 'string' || arg.length != 4 ||
            GH.typeOf(arg[0]) != 'string' || GH.typeOf(arg[1]) == 'string' ||
            GH.typeOf(arg[2]) == 'string') {
            throw "Expected 'stmt (LABEL ((TVAR BVAR ...) ...) (HYP ...) CONCL)'";
        }
        var local_label = arg[0];
        //log ('   ' + local_label);
        var fv = arg[1];
        var local_hyps = arg[2];
        var local_concl = arg[3];
        var label = this.prefix + local_label;

        if (!this.verify.syms.hasOwnProperty(label)) {
            throw ("An assertion '" + label +
                   "' does not exist in verify context.");
        }
        var vstmt = this.verify.syms[label];

        if (vstmt[0] != 'thm' && vstmt[0] != 'stmt') {
            throw ("The symbol '" + label + 
                   "' is not an assertion in verify context.");
        }
        if (this.assertions.hasOwnProperty(local_label)) {
            throw ("An assertion '" + local_label + 
                   "' has already been exported.");
        }
        
        // var vkw = vstmt[0];
        var vfv = vstmt[1];
        var vhyps = vstmt[2];
        var vconcl = vstmt[3];
        // var vmand = vstmt[4];
        // var vsyms = vstmt[5]
        
        if (local_hyps.length != vhyps.length) {
            throw ("The exported assertion '" + local_label + 
                   "' has " + local_hyps + 
                   " hypotheses, while its original has " + vhyps.length);
        }
        
        var varmap = {};
        var invmap = {};
        for (i = 0; i < vhyps.length; i++) {
            if (!this.export_match(local_hyps[i], vhyps[i], varmap, invmap)) {
                throw ('Hypothesis mismatch for stmt ' + local_label + 
                       ':\nExport context:\n   ' + 
                       GH.sexp_to_string(local_hyps[i]) +
                       '\nVerify context:\n   ' +
                       GH.sexp_to_string(vhyps[i]) + '\n');
            }
        }
        if (!this.export_match(local_concl, vconcl, varmap, invmap)) {
            throw ('Conclusion mismatch for stmt ' + local_label + 
                   ':\nExport context:\n   ' + 
                   GH.sexp_to_string(local_concl) +
                   '\nVerify context:\n   ' +
                   GH.sexp_to_string(vconcl) + '\n');
        }
        var nonfrees_orig = {};
        var tvar, bvar, clause;
        for (i = 0; i < vfv.length; i++) {
            clause = vfv[i];
            tvar = clause[0];
            for (j = 1; j < clause.length; j++) {
                bvar = clause[j];
                if (nonfrees_orig.hasOwnProperty(bvar)) {
                    nonfrees_orig[bvar][tvar] = 0;
                } else {
                    // had nonfrees_orig[bvar] = {tvar : 0}, doesn't work...
                    nonfrees_orig[bvar] = {};
                    nonfrees_orig[bvar][tvar] = 0;
                }
            }
        }
        var nonfrees = {};
        for (i = 0; i < fv.length; i++) {
            clause = fv[i];
            if (GH.typeOf(clause) == 'string' || clause.length < 2) {
                throw 'Each free variable constraint context clause must be a list of at least two variables.';
            }
            var want = 'tvar';
            for (j = 0; j < clause.length; j++) {
                v = clause[j];
                if (GH.typeOf(v) != 'string') {
                    throw 'Free variable constraint clause list elements must be variables';
                }
                if (!this.vars.hasOwnProperty(v)) {
                    throw 'Unknown variable ' + v;
                }
                if (!varmap.hasOwnProperty(v)) {
                    throw 'The variable ' + v + ' does not occur in the statement hypotheses or conclusions';
                }
                vv = this.vars[v];
                if (vv[0] != want) {
                    throw 'The first variable in a free variable constraint clause must be a term variable, and the remaining variables must be binding variables.';
                }
                if (want == 'tvar') {
                    tvar = varmap[v];
                } else {
                    bvar = varmap[v];
                    if (!nonfrees_orig.hasOwnProperty(bvar) ||
                        !nonfrees_orig[bvar].hasOwnProperty(tvar)) {
                        throw ("Export context free variable constraint (" +
                               clause[0] + " " + v + ") is unnecessary.");
                    }
                    if (nonfrees.hasOwnProperty(bvar)) {
                        nonfrees[bvar][tvar] = 0;
                    } else {
                        // nonfrees[bvar] = {tvar:0};
                        nonfrees[bvar] = {};
                        nonfrees[bvar][tvar] = 0;
                    }
                }
                want = 'var';
            }
        }
        // Check that all the constraints in nonfrees_orig occur in nonfrees
        for (bvar in nonfrees_orig) {
          if (nonfrees_orig.hasOwnProperty(bvar)) {
            var tvars = nonfrees_orig[bvar];
            for (tvar in tvars) {
              if (tvars.hasOwnProperty(tvar)) {
                if (!nonfrees.hasOwnProperty(bvar) ||
                    !nonfrees[bvar].hasOwnProperty(tvar)) {
                    throw ("Missing free variable constraint (" +
                           invmap[tvar] + ' ' + invmap[bvar] + ")");
                }
              }
            }
          }
        }
        this.assertions[local_label] = 0;
        return;
    }
    if (cmd == 'term') {
        // export context 'term' command
        if (GH.typeOf(arg) == 'string' || arg.length < 2) {
            throw "Expected 'term (KIND (NAME ARGVAR ...) (BARGVAR TARGVAR ...) ...'";
        }
        var term = GH.term_common(arg[0], arg[1], arg.slice(2), 
                                  this.kinds, this.terms, this.vars);

        var local_termname = arg[1][0];
        var termname = this.prefix + local_termname;

        // check that the term exists in verify context and that it
        // matches the one declared here.

        if (!this.verify.terms.hasOwnProperty(termname)) {
            throw 'No term of name ' + termname + ' exists in verify context.';
        }
        var vterm = this.verify.terms[termname];

        if (term[0] != vterm[0]) {
            throw ('Result kind mismatch with verify context for ' +
                   local_termname);
        }
        // Slightly abuse sexp_equals to compare argkinds
        if (!GH.sexp_equals(term[1], vterm[1])) {
            throw ('Term signature mismatch with verify context for ' + 
                   local_termname);
        }
        var freemap = term[2];
        var vfreemap = vterm[2];
        for (i = 0; i < freemap.length; i++) {
            var fm = freemap[i];
            var vfm = vfreemap[i];
            if (fm == null || vfm == null) {
                if (fm != null || vfm != null) {
                    throw ('binding/non-binding mismatch for term ' + 
                           local_termname + ' argument ' + i);
                }
                continue;
            }
            if (fm.length != vfm.length) {
                throw 'freemap mismatch for term ' + local_termname;
            }
            // note fm/vfm are sorted so they must agree exactly
            for (j = 0; j < fm.length; j++) {
                if (fm[j] != vfm[j]) {
                  throw 'freemap mismatch for term ' + local_termname;
                }
            }
        }
        this.terms[local_termname] = termname;
        this.myterms[local_termname] = termname;
        return;
    }
    if (cmd == 'kind') {
        // export context 'kind' command
        var prefixed_kind = this.kind_cmd_common(arg);
        // The prefixed kind must exist in verify context.
        kind = this.get_kind(prefixed_kind);
        this.mykinds[arg[0]] = kind;
        this.kinds[arg[0]] = kind;
        return;
    }
    if (cmd == 'var' || cmd == 'tvar') {
        this.var_cmd(cmd, arg);
        return;
    }
    if (cmd == 'param') {
        this.param_cmd(arg);
        return;
    }
    throw 'Unknown interface command ' + cmd;
};
