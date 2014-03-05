// Copyright 2010 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Laying out mathematics into typeset form.

GH.ENABLE_LATEX = true;
GH.REFRESH_LATEX = true;

// Conversion to either a simple HTML unicode string or a LaTex expression. This is useful
// both as a simple display method and also for cut-and-paste interoperation.
GH.sexptohtml = function(sexp, useLatex) {
	return GH.typeset(sexp, useLatex).str;
};

GH.escapeHtml = function(s) {
    return s
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;');
};

GH.min = function(x, y) {
    return x < y ? x : y;
};

GH.stringslug = function(str, useLatex) {
  return {str: str, prec: GH.typeset.maxPrec(useLatex), prsp: 0, tableSplit: false};
};

GH.spaceslug = function(sp, useLatex) {
    var em = sp * .06;
    if (em < .05) {
        return GH.stringslug('\u200b', useLatex);
    } else if (em < .133) {
        return GH.stringslug('\u200a', useLatex);
    } else if (em < .208) {
        return GH.stringslug('\u2006', useLatex);
    } else if (em < .292) {
        return GH.stringslug('\u2005', useLatex);
    } else if (em < .417) {
        return GH.stringslug('\u2004', useLatex);
    } else if (em < .75) {
        return GH.stringslug('\u2002', useLatex);
    } else {
        return GH.stringslug('\u2003', useLatex);
    }
};


// This is to ignore the .beg and .end part.
GH.strEquals = function(a, b) {
	if (a.length != b.length) {
		return false;
	}
	for (var i = 0; i < a.length; a++) {
		if (a[i] != b[i]) {
			return false;
		}
	}
	return true;
};

GH.combineslugs = function(slugs, prec, prsp) {
    var str = '';
	var tableSplit = false;
    for (var i = 0; i < slugs.length; i++) {
        str += slugs[i].str;
		tableSplit = tableSplit || slugs[i].tableSplit;
    }
    return {str: str, prec: prec, prsp: prsp || 0, tableSplit: tableSplit};
};

GH.parenthesize = function(slug, useLatex) {
	if (useLatex && !slug.tableSplit) {
		var lparen_slug = GH.stringslug('\\left(', useLatex);
		var rparen_slug = GH.stringslug('\\right)', useLatex);
	} else {
		var lparen_slug = GH.stringslug('(', useLatex);
		var rparen_slug = GH.stringslug(')', useLatex);
	}
    return GH.combineslugs([lparen_slug, slug, rparen_slug], GH.typeset.maxPrec(useLatex));
};

GH.typesetinfix = function(term, assoc, prec, op, useLatex) {
    var lprsp = 0;
    var rprsp = 0;
    var left_slug = GH.typeset(term[1], useLatex);
    var lprec = left_slug.prec;
    if (assoc == 'l') { lprec += 0.1; }
    if (prec >= lprec) {
        left_slug = GH.parenthesize(left_slug, useLatex);
        lprsp = 3;
    } else if (prec + 1 == lprec) {
        lprsp = left_slug.prsp;
    } else {
        lprsp = left_slug.prsp + 2;
    }
    var op_slug = GH.stringslug(op, useLatex);
    var right_slug = GH.typeset(term[2], useLatex);
    var rprec = right_slug.prec;
    if (assoc == 'r') { rprec += 0.1; }
    if (prec >= rprec) {
        right_slug = GH.parenthesize(right_slug, useLatex);
        rprsp = 3;
    } else if (prec + 0.1 == rprec) {
        rprsp = right_slug.prsp;
    } else {
        rprsp = right_slug.prsp + 2;
    }
    var prsp = GH.max(lprsp, GH.max(op_slug.prsp, rprsp));
    var sp_slug = GH.stringslug(' ', useLatex);
    var slugs = [left_slug, sp_slug, op_slug, sp_slug, right_slug];
    return GH.combineslugs(slugs, prec, prsp);
};

// USe the multiplication symbol when we are multiplying numbers like 2 * 13 or a * 2 or 1 * a,
// but not when we are multiplying variables like ab or 2a.
GH.typesetMultiply = function (term, prec, useLatex) {
	var sexp1 = GH.sExpression.fromRaw(term[1]);
	var reduced1 = GH.numUtil.isReduced(sexp1);
	var reduced2 = GH.numUtil.isReduced(GH.sExpression.fromRaw(term[2]));
	var num1 = GH.numUtil.decimalNumberSexp(sexp1)
	if (reduced2 || (reduced1 && ((num1 == 0) || (num1 == 1)))) {
		return GH.typesetinfix(term, 'l', prec, '\\cdot ', useLatex);
	} else {
		return GH.typesetinfix(term, 'l', prec, ' ', useLatex);
	}
};

// Convert expressions like (A < B) /\ (B < C) into A < B < C.
GH.typesetAnd = function (term, prec, useLatex) {
	if ((((term[1][0] == '<') || (term[1][0] == '<=')) &&
	     ((term[2][0] == '<') || (term[2][0] == '<='))) || 
		 ((term[1][0] == '=') && (term[2][0] == '='))) {
			 
		// This doesn't work for compound expressions like A < B + C < D.	
		if (term[1][2].toString() == term[2][1].toString()) {
			var operators = [];
			var operator = '';
			for (var i = 1; i < 3; i++) {
				if (term[i][0] == '<=') {
					operator = '≤';
				} else if (term[i][0] == '<') {
					operator = '&lt;';
				} else if (term[i][0] == '=') {
					operator = '=';
				}
				var space = GH.spaceslug(3, useLatex);
				operators.push(GH.combineslugs([space, GH.stringslug(operator, useLatex), space], prec));
			}
			var slug1 = GH.typeset(term[1][1], useLatex);
			var slug2 = GH.typeset(term[1][2], useLatex);
			var slug3 = GH.typeset(term[2][2], useLatex);
			return GH.combineslugs([slug1, operators[0], slug2, operators[1], slug3], prec);
		}
	}
    return GH.typesetinfix(term, 'r', prec, '∧', useLatex);
};

GH.typesetgeneric = function(term, prec, format, useLatex, useParentheses, noSpliting) {
	var slugs = [];
	for (var i = 0; i < format.length; i++) {
		// Format alternates between strings and terms.
		if (i % 2 == 0) {
			slugs.push(GH.stringslug(format[i], useLatex));
		} else {
			var termSlug = GH.typeset(term[format[i]], useLatex)
			if (useParentheses && (prec >= termSlug.prec)) {
		        termSlug = GH.parenthesize(termSlug, useLatex);
		    }
			if (termSlug.tableSplit && noSpliting) {
				return null;
			}
			slugs.push(termSlug);
		}
	}
    return GH.combineslugs(slugs, prec);
};

// First and third terms wrap the second term. Used to add html
// tags to the typesetting.
GH.typesettable = function(term, useLatex) {
    var pre_slug = GH.stringslug(term[1], useLatex);
    var main_slug = GH.typeset(term[2], useLatex);
    var post_slug = GH.stringslug(term[3], useLatex);
    var slugs = [pre_slug, main_slug, post_slug];
	main_slug.tableSplit = true;
    return GH.combineslugs(slugs, main_slug.prec, main_slug.prsp);                          
};

// Used to add color tags to the typesetting.
GH.typesetHtmlSpan = function(term, useLatex) {
	if (!useLatex) {
		var pre_slug = GH.stringslug('<span class=\'' + term[1] + '\'>');
		var main_slug = GH.typeset(term[2], useLatex);
		var post_slug = GH.stringslug('</span>');
		var slugs = [pre_slug, main_slug, post_slug];
		return GH.combineslugs(slugs, main_slug.prec, main_slug.prsp);
	} else {
		var pre_slug = GH.stringslug('\\class{' + term[1] + '}{');
		var main_slug = GH.typeset(term[2], useLatex);
		var post_slug = GH.stringslug('}');
		var slugs = [pre_slug, main_slug, post_slug];
		return GH.combineslugs(slugs, main_slug.prec, main_slug.prsp);
	}
};

GH.typesetapply = function(term, prec, useLatex) {
    var fun_slug = GH.typeset(term[1], useLatex);
	// Not sure why this was here. It's creating problems. Maybe there's a good reason for it.
	// if (prec >= fun_slug.prec, useLatex) {
    //     fun_slug = GH.parenthesize(fun_slug);
    // }
	var input = GH.typeset(term[2], useLatex);
    var input_slug = (term[2][0] == '<,>') ? input : GH.parenthesize(input, useLatex);
    var slugs = [fun_slug, input_slug];
    return GH.combineslugs(slugs, GH.min(prec, fun_slug.prec));
};

GH.typesetApplySet = function(term, useLatex) {
	if ((term[1][0] == 'lambda') && (term[2][0] == '{|}') && (GH.strEquals(term[1][1], term[2][1]))) {
		// This case is written like {S(x) | x = ...}
		var open_slug = GH.stringslug('{', useLatex);
    	var x_slug = GH.typeset(term[1][2], useLatex);
	    var slash_slug = GH.stringslug('|', useLatex);
    	var ph_slug = GH.typeset(term[2][2], useLatex);
	    var close_slug = GH.stringslug('}', useLatex);
    	var slugs = [open_slug, x_slug, slash_slug, ph_slug, close_slug];
	    return GH.combineslugs(slugs, GH.typeset.maxPrec(useLatex));
	} else {
		// This case is written like S(T).
		var fun_slug = GH.typeset(term[1], useLatex);
		//if (2500 >= fun_slug.prec) {
		//	fun_slug = GH.parenthesize(fun_slug, useLatex);
		//}
		var input_slug = GH.parenthesize(GH.typeset(term[2], useLatex));
		var slugs = [fun_slug, input_slug];
		return GH.combineslugs(slugs, fun_slug.prec);
	}
};

GH.typesetsum = function(term, prec, useLatex) {
	var bottomVariable;
	var application;
	if (term[3][0] == 'lambda') {
		bottomVariable = GH.typeset(term[3][1], useLatex).str + ' = ';
		application = GH.typeset(term[3][2], useLatex).str;
	} else {
		bottomVariable = '';
		application = GH.typeset(term[3], useLatex).str;
	}
	if (!useLatex) {
		return GH.typesetgeneric(term, prec, ['Σ <sub>' + bottomVariable, 1, '</sub><sup>', 2, '</sup>' + application], useLatex);
	} else {
		return GH.typesetgeneric(term, prec, ['\\sum_{' + bottomVariable, 1, '}^{', 2, '}' + application], useLatex);
	}
};

GH.typesetproduct = function(term, prec, useLatex) {
	var bottomVariable;
	var application;
	if (term[3][0] == 'lambda') {
		bottomVariable = GH.typeset(term[3][1], useLatex).str + ' = ';
		application = GH.typeset(term[3][2], useLatex).str;
	} else {
		bottomVariable = '';
		application = GH.typeset(term[3], useLatex).str;
	}
	if (!useLatex) {
		return GH.typesetgeneric(term, prec, ['Π <sub>' + bottomVariable, 1, '</sub><sup>', 2, '</sup>' + application], useLatex);
	} else {
		return GH.typesetgeneric(term, prec, ['\\prod_{' + bottomVariable, 1, '}^{', 2, '}' + application], useLatex);
	}
};

GH.isSetInExpectedForm = function(sexp) {
	return (sexp[0] == '{}') ||
           ((sexp[0] == 'u.') && GH.isSetInExpectedForm(sexp[1]) && (sexp[2][0] == '{}'));
};

GH.getSetElements = function(set, result) {
	if (set[0] == '{}'){
		result.push(set[1]);
		return result;
	} else {
		result = GH.getSetElements(set[1], result);
		result.push(set[2][1]);
		return result;
	}
};

GH.typesetSet = function(term, useLatex) {
	var slugs = [GH.stringslug('{', useLatex)];
	var elements = GH.getSetElements(term, []);
	for (var i = 0; i < elements.length; i++) {
		slugs.push(GH.typeset(elements[i], useLatex));
		if (i < elements.length - 1) {
		    slugs.push(GH.stringslug(',', useLatex));
		}
	}
    slugs.push(GH.stringslug('}', useLatex));
    return GH.combineslugs(slugs, GH.typeset.maxPrec(useLatex));
};

GH.getTupleElements = function(tuple, result) {
	if (tuple[1][0] == '<,>'){
		GH.getTupleElements(tuple[1], result);
	} else {
		result.push(tuple[1]);	
	}
	result.push(tuple[2]);
	return result;
};

GH.typesetTuple = function(term, prec, useLatex) {	
	var slugs = [GH.stringslug('(', useLatex)];
	var elements = GH.getTupleElements(term, []);
	for (var i = 0; i < elements.length; i++) {
		slugs.push(GH.typeset(elements[i], useLatex));
		if (i < elements.length - 1) {
		    slugs.push(GH.stringslug(', ', useLatex));
		}
	}
    slugs.push(GH.stringslug(')', useLatex));
    return GH.combineslugs(slugs, GH.typeset.maxPrec(useLatex));
};

GH.typesetVariables = function(sexp) {
	var trans = {
		et: 'η',
		th: 'θ',
		ta: 'τ',
		ph: 'φ',
		ch: 'χ',
		ps: 'ψ',
		ep: 'ϵ'
	};
	if (sexp in trans) {
		return trans[sexp];
	} else {
		return sexp;
	}
};

GH.typesetCategory = function(sexp, typesettingData, prec, useLatex) {	
	if (typesettingData[1] == 'infix') {
		return GH.typesetinfix(sexp, typesettingData[2], prec, typesettingData[3], useLatex);
	} else if ((typesettingData[1] == 'generic') || (typesettingData[1] == 'no-parentheses')) {
		var result = GH.typesetgeneric(sexp, prec, typesettingData[2], useLatex, typesettingData[1] == 'generic', typesettingData.length == 5);
		if (result) {
			return result;
		} else {
			return GH.typesetgeneric(sexp, prec, typesettingData[4], useLatex, typesettingData[3] == 'generic', false);
		}
	} else if (typesettingData[1] == 'string') {
		return GH.stringslug(typesettingData[2], useLatex);
	} else if (typesettingData[1] == 'and') {
		return GH.typesetAnd(sexp, prec, useLatex);
	} else if (typesettingData[1] == 'multiply') {
		return GH.typesetMultiply(sexp, prec, useLatex);
	} else if (typesettingData[1] == 'tuple') {
		return GH.typesetTuple(sexp, prec, useLatex);
	} else if (typesettingData[1] == 'applyset') {
		return GH.typesetApplySet(sexp, prec, useLatex);
	} else if (typesettingData[1] == 'apply') {
		return GH.typesetapply(sexp, prec, useLatex);
	} else if (typesettingData[1] == 'sum') {
		return GH.typesetsum(sexp, prec, useLatex);
	} else if (typesettingData[1] == 'product') {
		return GH.typesetproduct(sexp, prec, useLatex);
	} else {
		alert('No type setting defined for ' + typesettingData[1] + '.');
		return '';
	}
};

GH.getTypesettingData = function(Operations, symbol) {
	for (var prec = 0; prec < Operations.length; prec++) {
		for (var i = 0; i < Operations[prec].length; i++) {
			var typesettingData = Operations[prec][i];
			for (var j = 0; j < typesettingData[0].length; j++) {
				if (symbol == typesettingData[0][j]) {
					return {data: typesettingData, prec: prec};
				}
			}
		}
	}
	return null;
}

GH.typeset = function(sexp, useLatex) {
	var str;
	var decimal = GH.numUtil.decimalNumber(sexp);
	var operations = useLatex ? GH.typeset.LATEX_OPERATIONS : GH.typeset.OPERATIONS;
    if (GH.typeOf(sexp) == 'string') {
		var symbol = GH.typesetVariables(sexp);
        return GH.stringslug(symbol, useLatex);
    } else if (!isNaN(decimal)) {
		return GH.stringslug(decimal.toString(), useLatex);
    } else if (sexp[0] == 'table') {
        return GH.typesettable(sexp, useLatex);
    } else if (sexp[0] == 'htmlSpan') {
        return GH.typesetHtmlSpan(sexp, useLatex);
	} else if (GH.isSetInExpectedForm(sexp)) {
        return GH.typesetSet(sexp, useLatex);
    } else if (sexp[0] == '-.' || sexp[0] == '¬') {
		var negativeData = GH.getTypesettingData(GH.typeset.NEGATED_OPERATIONS, sexp[1][0]);
		if (negativeData) {
			var positiveData = GH.getTypesettingData(operations, sexp[1][0]);
			return GH.typesetCategory(sexp[1], negativeData.data, positiveData.prec, useLatex);			
		}		
		var typesettingData = GH.getTypesettingData(operations, sexp[0]);
		return GH.typesetCategory(sexp, typesettingData.data, typesettingData.prec, useLatex);
    } else {
		var typesettingData = GH.getTypesettingData(operations, sexp[0]);
		if (typesettingData) {
			return GH.typesetCategory(sexp, typesettingData.data, typesettingData.prec, useLatex);
		}
		var sexp0 = GH.escapeHtml(sexp[0]);
		if (useLatex) {
			sexp0 = '\\textrm{' + sexp0 + '} \\enspace ';
		}
		var slugs = [GH.stringslug('(', useLatex), GH.stringslug(sexp0, useLatex)];
		for (var i = 1; i < sexp.length; i++) {
			slugs.push(GH.stringslug(' ', useLatex));
			slugs.push(GH.typeset(sexp[i], useLatex));
		}
		slugs.push(GH.stringslug(')', useLatex));
		return GH.combineslugs(slugs, GH.typeset.maxPrec(useLatex)); 
	}
};

// Returns the maximum precedence.
GH.typeset.maxPrec = function(useLatex) {
	if (useLatex) {
		return GH.typeset.LATEX_OPERATIONS.length - 1;
	} else {
		return GH.typeset.OPERATIONS.length - 1;
	}
};

// The operations are grouped in order of precedence. All the matters is the relative
// precedence. The numbers give the old numerical value for the precedence.
GH.typeset.LATEX_OPERATIONS = [
[ // 10
	[['lambda', 'λ'], 'infix', 'n', '↦'],
],
[ // 100
	[['<->', '↔'], 'infix', 'n', '↔'],
],
[ // 250
	[['->', '→'], 'infix', 'r', '→'],
],
[ // 40
	[['A.', '∀'],  'generic', ['∀', 1, ' \\enspace ', 2]],
    [['E.', 'n.E.', 'z.E.', '∃'],  'generic', ['∃', 1, ' \\enspace ', 2]],
    [['E!', '∃!'], 'generic', ['∃!', 1, ' \\enspace ', 2]],
    [['E*', '∃*'], 'generic', ['∃*', 1, ' \\enspace ', 2]],
],
[ // 40
    [['[/]', 'n.[/]'], 'generic', ['[', 1, '/', 2, '] \\enspace ', 3]],
],
[ // 300
	[['\\/', '∨'], 'infix', 'r', '∨'],
],
[
	[['/\\', '∧'], 'and'],
], // 1000
[
	[['-.', '¬'], 'generic', ['¬', 1]],
],
[
	[['prime'], 'generic', ['', 1, '\\> \\textrm{ is prime}']],
	[['even'],  'generic', ['', 1, '\\> \\textrm{ is even}']],
	[['odd'],   'generic', ['', 1, '\\> \\textrm{ is odd}']],
	[['zpos', 'qpos', 'pos'], 'generic', ['', 1, '\\> \\textrm{ is positive}']], 
	[['zneg', 'qneg', 'neg'], 'generic', ['', 1, '\\> \\textrm{ is negative}']],
	[['upperbound'],  'generic', ['', 1, '\\> \\textrm{ is an upper bound of }']], 
	[['supremum'],    'generic', ['', 1, '\\> \\textrm{ is the supremum of }']],
],
[ // 1050
	[['=', 'n.=', '=n', 'z.=', 'q.=', 'r.=','=z', '=q', '=_'],    'infix', 'n', '='],
	[['n.=_'],    'infix', 'n', '=_\\mathbb{N}'],
	[['<=', 'n.<=', 'z.<=', 'q.<=', '<=z', '<=q', '≤'], 'infix', 'n', '≤'],
    [['<', '<z', '<q'],          'infix', 'n', '&lt;'],
    [['>=', '>=z', '>=q'],       'infix', 'n', '≥'],
    [['>',  '>z',  '>q'],        'infix', 'n', '>'],
    [['>'],                      'infix', 'n', '>'],
    [['|'],                      'infix', 'n', '|'],	
    [['e.', '∈'],               'infix', 'n', '∈'],	
    [['n.e.'],                   'infix', 'n', '∈_\\mathbb{N}'],
    [['C_', '⊆'],               'infix', 'n', '⊆'],
    [['C.', '⊂'],               'infix', 'n', '⊂'],	
    [['=mod'], 'generic', ['', 1, '\\equiv_{', 3, '} ', 2]],
],
[ // 2200
	[['+', 'n.+', 'z.+', 'r.+', '+z', '+q'], 'infix', 'l', '+'],
	[['.-', '-', '-q', 'z.-', 'q.-', 'r.-'], 'infix', 'l', '-'],  // Minus
],
[	
	[['-n', '-qn', 'z.-n', 'q.-n', 'r.-n'], 'generic', ['-', 1]],  // Negative Sign
],
[
	[['</>'],  'no-parentheses', ['\\frac{', 1, '}{' , 2, '}']],
],
[
	[['/', 'r./'], 'no-parentheses', ['\\frac{', 1, '}{' , 2, '}'], 'generic', ['', 1, '/' , 2, '']],
	// [['div'], 'infix', 'n', '÷'],
	[['div'], 'no-parentheses', ['\\frac{', 1, '}{' , 2, '}'], 'generic', ['', 1, '÷' , 2, '']],
],
[ // 2300
    [['*', 'n.*', 'z.*', 'r.*', '*z', '*q', '∙'], 'multiply'],
],
[
	[['sqrt'], 'no-parentheses', ['\\sqrt{', 1, '}']],
	[['abs'],  'no-parentheses', ['\\left| ', 1, '\\right| '], 'no-parentheses', ['| ', 1, '| ']],
],
[ // 2500
	[['exp'], 'generic', ['', 1, '^{', 2, '}']],
	[['mod'], 'infix', 'n', ' mod '],
	[['!'],   'generic', ['', 1, '!']],
    [['nCr'], 'no-parentheses', ['\\binom{', 1, '}{', 2, '}'], 'no-parentheses', ['( ', 1, ') ']],
    [['recursep'], 'no-parentheses', ['', 1, '^{', 2, '} (', 3, ') = ', 4]],
    [['recurse'], 'no-parentheses', ['', 1, '^{', 2, '} (', 3, ')']],
	[['ifn'], 'no-parentheses', [
	  '\\left\\{' +
        '\\begin{array}{ll}',
          2, ', & ', 1, ' \\\\',
          3, ', & \\textrm{otherwise}' +
         '\\end{array}' +
       '\\right.'
	 ], 'generic', '\\textrm{ifn} ', 1, ' \\enspace ', 2, ' \\enspace ', 3]
],
[
	[['_'], 'generic', ['', 1, '_{', 2, '}']],
],
[ // 3000
	[['fibonacci'], 'generic', ['F_{', 1, '}']],
	[['tri'], 'generic', ['T_{', 1, '}']],
	[['head', 'n.head'], 'generic', ['', 1, '_{h}']],
	[['tail', 'n.tail'], 'generic', ['', 1, '_{t}']],
	[['top'], 'generic', ['', 1, '_{t}']],
	[['bottom'], 'generic', ['', 1, '_{b}']],
	[['sup'], 'generic', ['\\textrm{sup}', 1]],
	[['n'],  'no-parentheses', ['\\textrm{n} \\left( ', 1,' \\right)']],
	[['ns'], 'no-parentheses', ['\\textrm{n} \\left( ', 1,' \\right)']],
	[['n-1'],  'no-parentheses', ['\\textrm{n}^{-1}\\left( ', 1,' \\right)']],
],
[
	[['i^i'], 'infix', 'l', '∩'],
	[['u.'],  'infix', 'l', '∪'],	
],
[ // 9999
	[['T'], 'generic', ['\\top']],
	[['F'], 'generic', ['\\bot']],
	[['N'], 'string', 'ℕ'],
	[['n.0'], 'string', '0_{N}'],
	[['n.1'], 'string', '1_{N}'],
	[['z.0'], 'string', '0_{Z}'],
	[['z.1'], 'string', '1_{Z}'],
	[['r.0'], 'string', '0_{R}'],
	[['r.1'], 'string', '1_{R}'],
	[['S'], 'generic', ['', 1, '′']],
	[['primeset'], 'string', '\\textrm{Primes}'],
    [['{|}'], 'no-parentheses', ['\\{', 1, '|', 2, '\\}']],
    [['n.{|}'], 'no-parentheses', ['\\{', 1, '|', 2, '\\}_\\mathbb{N}']],
    [['{...}'], 'generic', ['\\{', 1, '\\ldots ', 2, '\\}']],
    [['{}'], 'generic', ['\\{', 1, '\\}']],
	[['{/}'], 'string', '\\emptyset'],
	[['<,>', 'n.<,>'], 'tuple'],
	[['<>'], 'tuple'],
    [['<{}>'], 'generic', ['\\{', 1, '_{1},      ', 1, '_{2}, \\ldots, ', 1, '_N\\}']],
    [['<+>'],  'generic', ['\\{', 1, '_{1} +     ', 1, '_{2}+ \\cdots +', 1, '_N\\}']],
    [['<*>'],  'generic', ['\\{', 1, '_{1}\\cdot ', 1, '_{2}  \\cdots  ', 1, '_N\\}']],
	[['{.|}'], 'applyset'],
	[['apply'], 'apply'],
	[['sum'], 'sum'],
	[['product'], 'product'],
],[
	[['last one is never used'], 'generic', ['last one']]
]];


// The operations are grouped in order of precedence. All the matters is the relative
// precedence. The numbers give the old numerical value for the precedence.
GH.typeset.OPERATIONS = [
[ // 10
	[['lambda', 'λ'], 'infix', 'n', '↦'],
],
[ // 100
	[['<->', '↔'], 'infix', 'n', '↔'],
],
[ // 250
	[['->', '→'], 'infix', 'r', '→'],
],
[ // 40
	[['A.', '∀'],                  'generic', ['∀',  1, ' \u2005 ', 2]],
    [['E.', 'n.E.', 'z.E.', '∃'],  'generic', ['∃',  1, ' \u2005 ', 2]],
    [['E!', '∃!'],                 'generic', ['∃!', 1, ' \u2005 ', 2]],
    [['E*', '∃*'],                 'generic', ['∃*', 1, ' \u2005 ', 2]],
],
[ // 40
    [['[/]'], 'generic', ['[', 1, '/', 2, '] \u2005 ', 3]],
],
[ // 300
	[['\\/', '∨'], 'infix', 'r', '∨'],
],
[
	[['/\\', '∧'], 'and'],
], // 1000
[
	[['-.', '¬'], 'generic', ['¬', 1]],
],
[
	[['prime'], 'generic', ['', 1, ' is prime']],
	[['even'],  'generic', ['', 1, ' is even']],
	[['odd'],   'generic', ['', 1, ' is odd']],
	[['zpos', 'pos'],  'generic', ['', 1, ' is positive']],
	[['zneg', 'neg'],  'generic', ['', 1, ' is negative']],
	[['qpos'],  'generic', ['', 1, ' is positive']],
	[['qneg'],  'generic', ['', 1, ' is negative']],
	[['upperbound'], 'infix', 'n', ' is an upper bound of '],
	[['supremum'],   'infix', 'n', ' is the supremum of '],
],
[ // 1050
	[['=', 'n.=', '=n', 'z.=', 'q.=', 'r.=','=z', '=q', '=_'],    'infix', 'n', '='],
	[['<=', 'n.<=', 'z.<=', 'q.<=', '<=z', '<=q', '≤'], 'infix', 'n', '≤'],
    [['<', '<z', '<q'],          'infix', 'n', '&lt;'],
    [['>=', '>=z', '>=q'],       'infix', 'n', '≥'],
    [['>',  '>z',  '>q'],        'infix', 'n', '>'],
    [['>'],                      'infix', 'n', '>'],
    [['|'],                      'infix', 'n', '|'],	
    [['e.', '∈'],               'infix', 'n', '∈'],
    [['C_', '⊆'],               'infix', 'n', '⊆'],
    [['C.', '⊂'],               'infix', 'n', '⊂'],	
    [['=mod'], 'generic', ['', 1, '≡<sub>', 3, '</sub>', 2]],
],
[
	[['sqrt'],  'generic', ['√', 1]],	
	[['abs'],  'no-parentheses', ['| ', 1, '| ']],
],
[ // 2200
	[['+', 'n.+', 'z.+', 'r.+', '+z', '+q'], 'infix', 'l', '+'],
	[['.-', '-', '-q', 'z.-', 'q.-', 'r.-'], 'infix', 'l', '-'],  // Minus
],
[ // Not sure where to put fractions.
	[['</>'], 'infix', 'n', '/'],
],
[	
	[['-n', 'z.-n', 'q.-n', 'r.-n', '-qn'], 'generic', ['-', 1]],  // Negative Sign
],
[ // 2300
    [['*', 'n.*', 'z.*', 'r.*', '*z', '*q', '∙'], 'infix', 'l', '∙'],
    [['/', 'r./'], 'infix', 'l', '/'],
],
[ // 2500
	[['exp'], 'generic', ['', 1, '<sup>', 2, '</sup>']],
	[['mod'], 'infix', 'n', ' mod '],
	[['div'], 'infix', 'n', '÷'],
	[['!'],   'generic', ['', 1, '!']],
    [['nCr'], 'generic', ['(<sup>', 1, '</sup><sub>', 2, '</sub>)']],
    [['recursep'], 'no-parentheses', ['', 1, '<sup>', 2, '</sup>(', 3, ') = ', 4]],
    [['recurse'], 'no-parentheses', ['', 1, '<sup>', 2, '</sup>(', 3, ')']],
],
[
	[['_'], 'generic', ['', 1, '<sub>', 2, '</sub>']],
],
[ // 3000
	[['fibonacci'], 'generic', ['F <sub>', 1, '<sub>']],
	[['tri'], 'generic', ['T <sub>', 1, '<sub>']],
	[['head', 'n.head'], 'generic', ['', 1, '<sub>h</sub>']],
	[['tail', 'n.tail'], 'generic', ['', 1, '<sub>t</sub>']],
	[['top'], 'generic', ['', 1, '<sub>t</sub>']],
	[['bottom'], 'generic', ['', 1, '<sub>b</sub>']],
	[['sup'], 'generic', ['sup', 1]],
	[['n'],  'no-parentheses', ['n( ', 1,' )']],
	[['n-1'],  'no-parentheses', ['n<sup>-1</sup>( ', 1,' )']],
],
[
	[['i^i'], 'infix', 'l', '∩'],
	[['u.'],  'infix', 'l', '∪'],	
],
[ // 9999
	[['T'], 'string', 'T'],
	[['F'], 'string', 'F'],
	[['N'], 'string', 'ℕ'],
	[['n.0'], 'string', '0<sub>N</sub>'],
	[['n.1'], 'string', '1<sub>N</sub>'],
	[['z.0'], 'string', '0<sub>Z</sub>'],
	[['z.1'], 'string', '1<sub>Z</sub>'],
	[['r.0'], 'string', '0<sub>R</sub>'],
	[['r.1'], 'string', '1<sub>R</sub>'],
	[['S'], 'generic', ['', 1, '′']],
	[['primeset'], 'string', 'Primes'],
    [['{|}'], 'no-parentheses', ['{', 1, '|', 2, '}']],
    [['{...}'], 'generic', ['{', 1, '…', 2, '}']],
    [['{}'], 'generic', ['{', 1, '}']],
	[['{/}'], 'string', '∅'],
	[['<,>', 'n.<,>'], 'tuple'],
	[['<>'], 'tuple'],	
    [['<{}>'], 'generic', ['{', 1, '<sub>1</sub>,  ', 1, '<sub>2</sub>, …, ', 1, '<sub>N</sub>}']],
    [['<+>'],  'generic', ['',  1, '<sub>1</sub> + ', 1, '<sub>2</sub>+ ⋯ +', 1, '<sub>N</sub>']],
    [['<*>'],  'generic', ['',  1, '<sub>1</sub> ⋅ ', 1, '<sub>2</sub>  ⋯  ', 1, '<sub>N</sub>']],
	[['{.|}'], 'applyset'],
	[['apply'], 'apply'],
	[['sum'], 'sum'],
	[['product'], 'product'],
], [
	[['last one is never used'], 'generic', ['last one']]
]];

GH.typeset.NEGATED_OPERATIONS = [
[
	[['=', '=z', '=q', 'n.=', 'z.=', 'q.=', '=_'], 'infix', 'n', '≠'],
    [['e.', '∈'],             'infix', 'n', '∉'],
    [['C_', '⊆'],             'infix', 'n', '⊈'],
	[['E.', '∃'],             'generic', ['&#8708', 1, ' \u2005 ', 2]],
	[['C.', '⊂'],             'infix', 'n', '⊄'],
    [['|'],                    'infix', 'n', '∤'],
    [['prime'],                'generic', ['', 1, ' \\textrm{ is not prime}']],
    [['even'],                 'generic', ['', 1, ' \\textrm{ is not even}']],
    [['odd'],                  'generic', ['', 1, ' \\textrm{ is not odd}']],
    [['pos'],                  'generic', ['', 1, ' \\textrm{ is not positive}']],
    [['neg'],                  'generic', ['', 1, ' \\textrm{ is not negative}']],
    [['zpos'],                 'generic', ['', 1, ' \\textrm{ is not positive}']],
    [['zneg'],                 'generic', ['', 1, ' \\textrm{ is not negative}']],
    [['qpos'],                 'generic', ['', 1, ' \\textrm{ is not positive}']],
    [['qneg'],                 'generic', ['', 1, ' \\textrm{ is not negative}']],
    [['upperbound'],           'infix', 'n', ' is not an upper bound of '],
    [['supremum'],             'infix', 'n', ' is not the supremum of '],
]];
