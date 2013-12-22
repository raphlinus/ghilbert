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

// Conversion to a simple HTML unicode string. This is useful both as a
// simple display method and also for cut-and-paste interoperation.
GH.sexptohtml = function(sexp) {
	return GH.typeset(sexp).str;
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

GH.stringslug = function(str) {
  return {str: str, prec: GH.typeset.MAX_PREC, prsp: 0};
};

GH.spaceslug = function(sp) {
    var em = sp * .06;
    if (em < .05) {
        return GH.stringslug('\u200b');
    } else if (em < .133) {
        return GH.stringslug('\u200a');
    } else if (em < .208) {
        return GH.stringslug('\u2006');
    } else if (em < .292) {
        return GH.stringslug('\u2005');
    } else if (em < .417) {
        return GH.stringslug('\u2004');
    } else if (em < .75) {
        return GH.stringslug('\u2002');
    } else {
        return GH.stringslug('\u2003');
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
    for (var i = 0; i < slugs.length; i++) {
        str += slugs[i].str;
    }
    return {str: str, prec: prec, prsp: prsp || 0};
};

GH.parenthesize = function(slug) {
    var lparen_slug = GH.stringslug('(');
    var rparen_slug = GH.stringslug(')');
    return GH.combineslugs([lparen_slug, slug, rparen_slug], GH.typeset.MAX_PREC);
};

GH.typesetinfix = function(term, assoc, prec, op) {
    var lprsp = 0;
    var rprsp = 0;
    var left_slug = GH.typeset(term[1]);
    var lprec = left_slug.prec;
    if (assoc == 'l') { lprec += 0.1; }
    if (prec >= lprec) {
        left_slug = GH.parenthesize(left_slug);
        lprsp = 3;
    } else if (prec + 1 == lprec) {
        lprsp = left_slug.prsp;
    } else {
        lprsp = left_slug.prsp + 2;
    }
    var op_slug = GH.stringslug(op);
    var right_slug = GH.typeset(term[2]);
    var rprec = right_slug.prec;
    if (assoc == 'r') { rprec += 0.1; }
    if (prec >= rprec) {
        right_slug = GH.parenthesize(right_slug);
        rprsp = 3;
    } else if (prec + 0.1 == rprec) {
        rprsp = right_slug.prsp;
    } else {
        rprsp = right_slug.prsp + 2;
    }
    var prsp = GH.max(lprsp, GH.max(op_slug.prsp, rprsp));
    var sp_slug = GH.spaceslug(GH.max(0, prsp));
    var slugs = [left_slug, sp_slug, op_slug, sp_slug, right_slug];
    return GH.combineslugs(slugs, prec, prsp);
};

GH.typesetunary = function(term, prec, op) {
    var op_slug = GH.stringslug(op);
    var right_slug = GH.typeset(term[1]);
    if (prec > right_slug.prec) {
        right_slug = GH.parenthesize(right_slug);
    }
    return GH.combineslugs([op_slug, right_slug], prec, 1);
};

GH.typesetpostfix = function(term, prec, op) {
    var op_slug = GH.stringslug(op);
    var right_slug = GH.typeset(term[1]);
    if (prec > right_slug.prec) {
        right_slug = GH.parenthesize(right_slug);
    }
    return GH.combineslugs([right_slug, op_slug], prec, 1);
};

// Convert expressions like (A < B) /\ (B < C) into A < B < C.
GH.typesetAnd = function (term, prec) {
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
				var space = GH.spaceslug(3);
				operators.push(GH.combineslugs([space, GH.stringslug(operator), space], prec));
			}
			var slug1 = GH.typeset(term[1][1]);
			var slug2 = GH.typeset(term[1][2]);
			var slug3 = GH.typeset(term[2][2]);
			return GH.combineslugs([slug1, operators[0], slug2, operators[1], slug3], prec);
		}
	}
    return GH.typesetinfix(term, 'r', prec, '∧');
};

GH.typesetbinder = function(term, prec, op) {
    var op_slug = GH.stringslug(op);
    var var_slug = GH.typeset(term[1]);
    var body_slug = GH.typeset(term[2]);
    var sp_slug = GH.spaceslug(1 + body_slug.prsp);
    var slugs = [op_slug, var_slug, sp_slug, body_slug];
    return GH.combineslugs(slugs, prec);
};

GH.typesetsubst = function(term, prec) {
    var open_slug = GH.stringslug('[');
    var A_slug = GH.typeset(term[1]);
    var slash_slug = GH.stringslug('/');
    var x_slug = GH.typeset(term[2]);
    var close_slug = GH.stringslug(']');
    var ph_slug = GH.typeset(term[3]);
    var sp_slug = GH.spaceslug(1 + ph_slug.prsp);
    var slugs = [open_slug, A_slug, slash_slug, x_slug, close_slug, 
             sp_slug, ph_slug];
    return GH.combineslugs(slugs, prec);                          
};

// First and third terms wrap the second term. Used to add html
// tags to the typesetting.
GH.typesettable = function(term) {
    var pre_slug = {str: term[1]};
    var main_slug = GH.typeset(term[2]);
    var post_slug = {str: term[3]};
    var slugs = [pre_slug, main_slug, post_slug];
    return GH.combineslugs(slugs, main_slug.prec, main_slug.prsp);                          
};

// Used to add color tags to the typesetting.
GH.typesetHtmlSpan = function(term) {
    var pre_slug = {str: '<span class=\'' + term[1] + '\'>'};
    var main_slug = GH.typeset(term[2]);
    var post_slug = {str: '</span>'};
    var slugs = [pre_slug, main_slug, post_slug];
    return GH.combineslugs(slugs, main_slug.prec, main_slug.prsp);                          
};

GH.typesetclab = function(term) {
    var open_slug = GH.stringslug('{');
    var x_slug = GH.typeset(term[1]);
    var slash_slug = GH.stringslug('|');
    var ph_slug = GH.typeset(term[2]);
    var close_slug = GH.stringslug('}');
    var slugs = [open_slug, x_slug, slash_slug, ph_slug, close_slug];
    return GH.combineslugs(slugs, GH.typeset.MAX_PREC);
};

GH.typesetInterval = function(term) {
    var open_slug = GH.stringslug('{');
    var x_slug = GH.typeset(term[1]);
    var slash_slug = GH.stringslug('...');
    var ph_slug = GH.typeset(term[2]);
    var close_slug = GH.stringslug('}');
    var slugs = [open_slug, x_slug, slash_slug, ph_slug, close_slug];
    return GH.combineslugs(slugs, GH.typeset.MAX_PREC);
};

GH.typesetsingleton = function(term) {
    var open_slug = GH.stringslug('{');
    var A_slug = GH.typeset(term[1]);
    var close_slug = GH.stringslug('}');
    var slugs = [open_slug, A_slug, close_slug];
    return GH.combineslugs(slugs, GH.typeset.MAX_PREC);
};

GH.typesetop = function(term) {
    var open_slug = GH.stringslug('⟨');
    var x_slug = GH.typeset(term[1]);
    var comma_slug = GH.stringslug(',');
    var y_slug = GH.typeset(term[2]);
    var sp_slug = GH.spaceslug(1 + y_slug.prsp);
    var close_slug = GH.stringslug('⟩');
    var slugs = [open_slug, x_slug, comma_slug, sp_slug, y_slug, close_slug];
    return GH.combineslugs(slugs, GH.typeset.MAX_PREC);
};

GH.typesetexp = function(term, prec) {
    var x_slug = GH.typeset(term[1]);
    if (prec >= x_slug.prec) {
        x_slug = GH.parenthesize(x_slug);
    }
    var sup_slug = GH.stringslug('<sup>');
    var y_slug = GH.typeset(term[2]);
    var endsup_slug = GH.stringslug('</sup>');
    var slugs = [x_slug, sup_slug, y_slug, endsup_slug];
    return GH.combineslugs(slugs, GH.min(prec, x_slug.prec));
};

GH.typesetBinomial = function(term, prec) {
    var top1_slug = GH.stringslug('<sup>');
    var top2_slug = GH.typeset(term[1]);
    var top3_slug = GH.stringslug('</sup>');
    var bot1_slug = GH.stringslug('<sub>');
    var bot2_slug = GH.typeset(term[2]);
    var bot3_slug = GH.stringslug('</sub>');
    var slugs = [top1_slug, top2_slug, top3_slug, bot1_slug, bot2_slug, bot3_slug];
    return GH.parenthesize(GH.combineslugs(slugs, prec));
};

GH.subscriptSlug = function(slug) {
	var start_slug = GH.stringslug('<sub>');
    var end_slug = GH.stringslug('</sub>');
    var slugs = [start_slug, slug, end_slug];
    return GH.combineslugs(slugs, GH.typeset.MAX_PREC);
};

GH.typesetindex = function(term, prec) {
    var x_slug = GH.typeset(term[1]);
    if (prec >= x_slug.prec) {
        x_slug = GH.parenthesize(x_slug);
    }
	var subscript = GH.subscriptSlug(GH.typeset(term[2]));
    var slugs = [x_slug, subscript];
    return GH.combineslugs(slugs, GH.min(prec, x_slug.prec));
};

GH.typesetStrIndex = function(term, name, prec) {	
    var f_slug = GH.stringslug(name);
	var index = GH.subscriptSlug(GH.typeset(term[1]));
    return GH.combineslugs([f_slug, index], prec);
};

GH.typesetrecursep = function(term, prec) {
    var recursep_slug = GH.stringslug('recursep ');
    var fun_slug = GH.typeset(term[1]);
    if (prec >= fun_slug.prec) {
        fun_slug = GH.parenthesize(fun_slug);
    }
    var sup_slug = GH.stringslug('<sup>');
    var y_slug = GH.typeset(term[2]);
    var endsup_slug = GH.stringslug('</sup>(');
    var input_slug = GH.typeset(term[3]);
    var end_input_slug = GH.stringslug(') = ');
    var output_slug = GH.typeset(term[4]);
    var slugs = [recursep_slug, fun_slug, sup_slug, y_slug, endsup_slug, input_slug, end_input_slug, output_slug];
    return GH.combineslugs(slugs, GH.min(prec, fun_slug.prec));
};

GH.typesetrecurse = function(term, prec) {
    var fun_slug = GH.typeset(term[1]);
    if (prec >= fun_slug.prec) {
        fun_slug = GH.parenthesize(fun_slug);
    }
    var sup_slug = GH.stringslug('<sup>');
	// TODO: Fix problem with selecting this part of the expression.
    var y_slug = GH.typeset(term[2]);
    var endsup_slug = GH.stringslug('</sup>');
	var input = GH.typeset(term[3]);
    var input_slug = (term[3][0] == '<,>') ? input : GH.parenthesize(input);
    var slugs = [fun_slug, sup_slug, y_slug, endsup_slug, input_slug];
    return GH.combineslugs(slugs, GH.min(prec, fun_slug.prec));
};

GH.typesetapply = function(term, prec) {
    var fun_slug = GH.typeset(term[1]);
	if (prec >= fun_slug.prec) {
        fun_slug = GH.parenthesize(fun_slug);
    }
	var input = GH.typeset(term[2]);
    var input_slug = (term[2][0] == '<,>') ? input : GH.parenthesize(input);
    var slugs = [fun_slug, input_slug];
    return GH.combineslugs(slugs, GH.min(prec, fun_slug.prec));
};

GH.typesetApplySet = function(term) {
	if ((term[1][0] == 'lambda') && (term[2][0] == '{|}') && (GH.strEquals(term[1][1], term[2][1]))) {
		// This case is written like {S(x) | x = ...}
		var open_slug = GH.stringslug('{');
    	var x_slug = GH.typeset(term[1][2]);
	    var slash_slug = GH.stringslug('|');
    	var ph_slug = GH.typeset(term[2][2]);
	    var close_slug = GH.stringslug('}');
    	var slugs = [open_slug, x_slug, slash_slug, ph_slug, close_slug];
	    return GH.combineslugs(slugs, GH.typeset.MAX_PREC);
	} else {
		// This case is written like S(T).
		var fun_slug = GH.typeset(term[1]);
		//if (2500 >= fun_slug.prec) {
		//	fun_slug = GH.parenthesize(fun_slug);
		//}
		var input_slug = GH.parenthesize(GH.typeset(term[2]));
		var slugs = [fun_slug, input_slug];
		return GH.combineslugs(slugs, fun_slug.prec);
	}
};

GH.typesetsum = function(term) {
	var bottomVariable;
	var application;
	if (term[3][0] == 'lambda') {
		bottomVariable = GH.combineslugs([GH.typeset(term[3][1]), GH.stringslug('=')], GH.typeset.MAX_PREC);
		application = GH.typeset(term[3][2]);
	} else {
		bottomVariable = GH.stringslug('');
		application = GH.typeset(term[3]);
	}	
	
	var bottom0 = GH.stringslug('<sub>');
	var bottom1 = GH.typeset(term[1]);
	var bottom2 = GH.stringslug('</sub>');
	var bottom = GH.combineslugs([bottom0, bottomVariable, bottom1, bottom2], GH.typeset.MAX_PREC);

	var top0 = GH.stringslug('<sup>');
	var top1 = GH.typeset(term[2]);
	var top2 = GH.stringslug('</sup>');
	var top = GH.combineslugs([top0, top1, top2], GH.typeset.MAX_PREC);

	var sigma = GH.stringslug('Σ');
	
	
    var slugs = [sigma, bottom, top, application];
    return GH.combineslugs(slugs, GH.typeset.MAX_PREC);
};

GH.typesetproduct = function(term) {
	var bottomVariable;
	var application;
	if (term[3][0] == 'lambda') {
		bottomVariable = GH.combineslugs([GH.typeset(term[3][1]), GH.stringslug('=')], GH.typeset.MAX_PREC);
		application = GH.typeset(term[3][2]);
	} else {
		bottomVariable = GH.stringslug('');
		application = GH.typeset(term[3]);
	}	
	
	var bottom0 = GH.stringslug('<sub>');
	var bottom1 = GH.typeset(term[1]);
	var bottom2 = GH.stringslug('</sub>');
	var bottom = GH.combineslugs([bottom0, bottomVariable, bottom1, bottom2], GH.typeset.MAX_PREC);

	var top0 = GH.stringslug('<sup>');
	var top1 = GH.typeset(term[2]);
	var top2 = GH.stringslug('</sup>');
	var top = GH.combineslugs([top0, top1, top2], GH.typeset.MAX_PREC);

	var sigma = GH.stringslug('Π');	
	
    var slugs = [sigma, bottom, top, application];
    return GH.combineslugs(slugs, GH.typeset.MAX_PREC);
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

GH.typesetSet = function(term) {
	var slugs = [GH.stringslug('{')];
	var elements = GH.getSetElements(term, []);
	for (var i = 0; i < elements.length; i++) {
		slugs.push(GH.typeset(elements[i]));
		if (i < elements.length - 1) {
		    slugs.push(GH.stringslug(','));
		}
	}
    slugs.push(GH.stringslug('}'));
    return GH.combineslugs(slugs, GH.typeset.MAX_PREC);
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

GH.typesetTuple = function(term) {	
	var slugs = [GH.stringslug('(')];
	var elements = GH.getTupleElements(term, []);
	for (var i = 0; i < elements.length; i++) {
		slugs.push(GH.typeset(elements[i]));
		if (i < elements.length - 1) {
		    slugs.push(GH.stringslug(','));
		}
	}
    slugs.push(GH.stringslug(')'));
    return GH.combineslugs(slugs, GH.typeset.MAX_PREC);
};

// TODO: Change type setting when its a tuple with the length is specified.
GH.typesetTupleOperation = function(term, start, operator, dots, end) {	
    var slug1 = GH.subscriptSlug(GH.stringslug('1'));
    var slug2 = GH.subscriptSlug(GH.stringslug('2'));
	// N is used to denote that this is a set with some arbitrary finite length.
	// Currently, N is not being used for anything. We may need to revisit this.
    var slugN = GH.subscriptSlug(GH.stringslug('N'));
    var opSlug = GH.stringslug(operator);
	var slugTerm = GH.typeset(term[1]);
	var slugDots;
	if (operator == '∙') {
		slugDots = GH.stringslug(dots);
	} else {
		slugDots = GH.combineslugs([opSlug, GH.stringslug(dots), opSlug], GH.typeset.MAX_PREC);
	}
	var slugs = [GH.stringslug(start), slugTerm, slug1, opSlug, slugTerm, slug2,
	             slugDots, slugTerm, slugN, GH.stringslug(end)];
    return GH.combineslugs(slugs, GH.typeset.MAX_PREC);
};

GH.typesetVariables = function(sexp) {
	var trans = {
		et: 'η',
		th: 'θ',
		ta: 'τ',
		ph: 'φ',
		ch: 'χ',
		ps: 'ψ'
	};
	if (sexp in trans) {
		return trans[sexp];
	} else {
		return sexp;
	}
};

GH.typesetCategory = function(sexp, typesettingData, prec) {	
	if (typesettingData[1] == 'infix') {
		return GH.typesetinfix(sexp, typesettingData[2], prec, typesettingData[3]);
	} else if (typesettingData[1] == 'postfix') {
		return GH.typesetpostfix(sexp, prec, typesettingData[2]);
	} else if (typesettingData[1] == 'unary') {
		return GH.typesetunary(sexp, prec, typesettingData[2]);
	} else if (typesettingData[1] == 'binder') {
		return GH.typesetbinder(sexp, prec, typesettingData[2]);
	} else if (typesettingData[1] == 'subst') {
		return GH.typesetsubst(sexp, prec);
	} else if (typesettingData[1] == 'string') {
		return GH.stringslug(typesettingData[2]);
	} else if (typesettingData[1] == 'and') {
		return GH.typesetAnd(sexp, prec);
	} else if (typesettingData[1] == 'exp') {
		return GH.typesetexp(sexp, prec);
	} else if (typesettingData[1] == 'binomial') {
		return GH.typesetBinomial(sexp, prec);
	} else if (typesettingData[1] == 'recursep') {
		return GH.typesetrecursep(sexp, prec);
	} else if (typesettingData[1] == 'recurse') {
		return GH.typesetrecurse(sexp, prec);
	} else if (typesettingData[1] == 'index') {
		return GH.typesetindex(sexp, prec);
	} else if (typesettingData[1] == 'strIndex') {
		return GH.typesetStrIndex(sexp, typesettingData[2], prec);
	} else if (typesettingData[1] == 'clab') {
		return GH.typesetclab(sexp, prec);
	} else if (typesettingData[1] == 'interval') {
		return GH.typesetInterval(sexp, prec);
	} else if (typesettingData[1] == 'singleton') {
		return GH.typesetsingleton(sexp, prec);
	} else if (typesettingData[1] == 'tuple') {
		return GH.typesetTuple(sexp, prec);
	} else if (typesettingData[1] == 'tupleOperation') {
		return GH.typesetTupleOperation(sexp, typesettingData[2], typesettingData[3], typesettingData[4], typesettingData[5]);
	} else if (typesettingData[1] == 'applyset') {
		return GH.typesetApplySet(sexp, prec);
	} else if (typesettingData[1] == 'apply') {
		return GH.typesetapply(sexp, prec);
	} else if (typesettingData[1] == 'sum') {
		return GH.typesetsum(sexp, prec);
	} else if (typesettingData[1] == 'product') {
		return GH.typesetproduct(sexp, prec);
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

GH.typeset = function(sexp) {
	var str;
	var decimal = GH.numUtil.decimalNumber(sexp);
    if (GH.typeOf(sexp) == 'string') {
		var symbol = GH.typesetVariables(sexp);
        return GH.stringslug(symbol);
    } else if (!isNaN(decimal)) {
		return GH.stringslug(decimal.toString());
    } else if (sexp[0] == 'table') {
        return GH.typesettable(sexp);
    } else if (sexp[0] == 'htmlSpan') {
        return GH.typesetHtmlSpan(sexp);
	} else if (GH.isSetInExpectedForm(sexp)) {
        return GH.typesetSet(sexp);
    } else if (sexp[0] == '-.' || sexp[0] == '¬') {
		var negativeData = GH.getTypesettingData(GH.typeset.NEGATED_OPERATIONS, sexp[1][0]);
		if (negativeData) {
			var positiveData = GH.getTypesettingData(GH.typeset.OPERATIONS, sexp[1][0]);
			return GH.typesetCategory(sexp[1], negativeData.data, positiveData.prec);			
		}		
		var typesettingData = GH.getTypesettingData(GH.typeset.OPERATIONS, sexp[0]);
		return GH.typesetCategory(sexp, typesettingData.data, typesettingData.prec);
    } else {
		var typesettingData = GH.getTypesettingData(GH.typeset.OPERATIONS, sexp[0]);
		if (typesettingData) {
			return GH.typesetCategory(sexp, typesettingData.data, typesettingData.prec);
		}
		var slugs = [GH.stringslug('('), GH.stringslug(GH.escapeHtml(sexp[0]))];
		for (var i = 1; i < sexp.length; i++) {
			slugs.push(GH.stringslug(' '));
			slugs.push(GH.typeset(sexp[i]));
		}
		slugs.push(GH.stringslug(')'));
		return GH.combineslugs(slugs, GH.typeset.MAX_PREC); 
	}
};

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
	[['A.', '∀'],  'binder', '∀'],
    [['E.', '∃'],  'binder', '∃'],
    [['E!', '∃!'], 'binder', '∃!'],
    [['E*', '∃*'], 'binder', '∃*'],
],
[ // 40
    [['[/]'], 'subst'],
],
[ // 300
	[['\\/', '∨'], 'infix', 'r', '∨'],
],
[
	[['/\\', '∧'], 'and'],
], // 1000
[
	[['-.', '¬'], 'unary', '¬'],
],
[
	[['prime'], 'postfix', ' is prime'],
],
[ // 1050
	[['=', '=z', '=q', '=_'],    'infix', 'n', '='],
	[['<=', '<=z', '<=q', '≤'], 'infix', 'n', '≤'],
    [['<', '<z', '<q'],          'infix', 'n', '&lt;'],
    [['>='],                     'infix', 'n', '≥'],
    [['>'],                      'infix', 'n', '>'],
    [['|'],                      'infix', 'n', '|'],	
    [['e.', '∈'],               'infix', 'n', '∈'],
    [['C_', '⊆'],               'infix', 'n', '⊆'],
    [['C.', '⊂'],               'infix', 'n', '⊂'],
],
[ // 2200
	[['+', '+z', '+q'], 'infix', 'l', '+'],
	[['.-', '-'],       'infix', 'l', '-'],  // Minus
],
[ // Not sure where to put fractions.
	[['</>'], 'infix', 'n', '/'],
],
[	
	[['-n'], 'unary', '-'],  // Negative Sign
],
[ // 2300
    [['*', '*z', '*q', '∙'], 'infix', 'l', '∙'],
],
[ // 2500
	[['exp'], 'exp'],
	[['mod'], 'infix', 'n', ' mod '],
	[['div'], 'infix', 'n', '÷'],
	[['!'],   'postfix', '!'],
    [['nCr'], 'binomial'],
    [['recursep'], 'recursep'],
    [['recurse'], 'recurse'],
],
[
	[['_'], 'index'],
],
[ // 3000
	[['fibonacci'], 'strIndex', 'F'],
	[['tri'], 'strIndex', 'T'],
	[['head'], 'postfix', '<sub>h</sub>'],
	[['tail'], 'postfix', '<sub>t</sub>'],
],
[
	[['i^i'], 'infix', 'l', '∩'],
	[['u.'],  'infix', 'l', '∪'],	
],
[ // 9999
	[['T'], 'string', 'T'],
	[['F'], 'string', 'F'],
	[['S'], 'postfix', '′'],
	[['primeset'], 'string', 'Primes'],
    [['{|}'], 'clab'],
    [['{...}'], 'interval'],
    [['{}'], 'singleton'],
	[['{/}'], 'string', '∅'],
	[['<,>'], 'tuple'],
	[['<>'], 'tuple'],
	[['<{}>'], 'tupleOperation', '{', ',', '…', '}'],
	[['<+>'],  'tupleOperation', '', '+', '…', ''],
	[['<*>'],  'tupleOperation', '', '∙', '⋯', ''],
	[['{.|}'], 'applyset'],
	[['apply'], 'apply'],
	[['sum'], 'sum'],
	[['product'], 'product'],
]];

// The maximum precedence
GH.typeset.MAX_PREC  = GH.typeset.OPERATIONS.length - 1;

GH.typeset.NEGATED_OPERATIONS = [
[
	[['=', '=z', '=q', '=_'], 'infix', 'n', '≠'],
    [['e.', '∈'],             'infix', 'n', '∉'],
    [['C_', '⊆'],             'infix', 'n', '⊈'],
	[['E.', '∃'],             'binder', '&#8708'],
	[['C.', '⊂'],             'infix', 'n', '⊄'],
    [['|'],                    'infix', 'n', '∤'],
    [['prime'],                'postfix', ' is not prime'],
]];
