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

// Highlights the s-expression at the cursor position.
GH.sexptohtmlHighlighted = function(sexp, cursorPosition) {
  return GH.typeset(sexp, cursorPosition).str;
};

// Conversion to a simple HTML unicode string. This is useful both as a
// simple display method and also for cut-and-paste interoperation.
GH.sexptohtml = function(sexp) {
	return GH.sexptohtmlHighlighted(sexp, -1);
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
  return {str: str, prec: 9999, prsp: 0};
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
    return GH.combineslugs([lparen_slug, slug, rparen_slug], 9999);
};

// Highlight part of the text.
GH.highlightSymbol = function(str, term, cursorPosition) {
	if (term.beg && term.end && (term.beg <= cursorPosition) && (cursorPosition <= term.end)) {
		return '<span class=\'highlight-symbol\'>' + str + '</span>';
	} else {
		return str;
	}
};

GH.typesetinfix = function(term, assoc, prec, op, cursorPosition) {
		op = GH.highlightSymbol(op, term[0], cursorPosition);

    var lprsp = 0;
    var rprsp = 0;
    var left_slug = GH.typeset(term[1], cursorPosition);
    var lprec = left_slug.prec;
    if (assoc == 'l') { lprec += 1; }
    if (prec >= lprec) {
        left_slug = GH.parenthesize(left_slug);
        lprsp = 3;
    } else if (prec + 1 == lprec) {
        lprsp = left_slug.prsp;
    } else {
        lprsp = left_slug.prsp + 2;
    }
    var op_slug = GH.stringslug(op);
    var right_slug = GH.typeset(term[2], cursorPosition);
    var rprec = right_slug.prec;
    if (assoc == 'r') { rprec += 1; }
    if (prec >= rprec) {
        right_slug = GH.parenthesize(right_slug);
        rprsp = 3;
    } else if (prec + 1 == rprec) {
        rprsp = right_slug.prsp;
    } else {
        rprsp = right_slug.prsp + 2;
    }
    var prsp = GH.max(lprsp, GH.max(op_slug.prsp, rprsp));
    var sp_slug = GH.spaceslug(GH.max(0, prsp));
    var slugs = [left_slug, sp_slug, op_slug, sp_slug, right_slug];
    return GH.combineslugs(slugs, prec, prsp);
};

GH.typesetunary = function(term, prec, op, cursorPosition) {
    var op_slug = GH.stringslug(op);
    var right_slug = GH.typeset(term[1], cursorPosition);
    if (prec > right_slug.prec) {
        right_slug = GH.parenthesize(right_slug);
    }
    return GH.combineslugs([op_slug, right_slug], prec, 1);
};

GH.typesetpostfix = function(term, prec, op, cursorPosition) {

    var op_slug = GH.stringslug(op);
    var right_slug = GH.typeset(term[1], cursorPosition);
    if (prec > right_slug.prec) {
        right_slug = GH.parenthesize(right_slug);
    }
    return GH.combineslugs([right_slug, op_slug], prec, 1);
};

GH.typesetbinder = function(term, prec, op, cursorPosition) {
    var op_slug = GH.stringslug(op);
    var var_slug = GH.typeset(term[1], cursorPosition);
    var body_slug = GH.typeset(term[2], cursorPosition);
    var sp_slug = GH.spaceslug(1 + body_slug.prsp);
    var slugs = [op_slug, var_slug, sp_slug, body_slug];
    return GH.combineslugs(slugs, prec);
};

GH.typesetsubst = function(term, prec, cursorPosition) {
    var open_slug = GH.stringslug('[');
    var A_slug = GH.typeset(term[1], cursorPosition);
    var slash_slug = GH.stringslug('/');
    var x_slug = GH.typeset(term[2], cursorPosition);
    var close_slug = GH.stringslug(']');
    var ph_slug = GH.typeset(term[3], cursorPosition);
    var sp_slug = GH.spaceslug(1 + ph_slug.prsp);
    var slugs = [open_slug, A_slug, slash_slug, x_slug, close_slug, 
             sp_slug, ph_slug];
    return GH.combineslugs(slugs, prec);                          
};

// First and third terms wrap the second term. Used to add html
// tags to the typesetting.
GH.typesettable = function(term, cursorPosition) {
    var pre_slug = {str: term[1]};
    var main_slug = GH.typeset(term[2], cursorPosition);
    var post_slug = {str: term[3]};
    var slugs = [pre_slug, main_slug, post_slug];
    return GH.combineslugs(slugs, main_slug.prec, main_slug.prsp);                          
};

// Used to add color tags to the typesetting.
GH.typesetHtmlSpan = function(term, cursorPosition) {
    var pre_slug = {str: '<span class=\'' + term[1] + '\'>'};
    var main_slug = GH.typeset(term[2], cursorPosition);
    var post_slug = {str: '</span>'};
    var slugs = [pre_slug, main_slug, post_slug];
    return GH.combineslugs(slugs, main_slug.prec, main_slug.prsp);                          
};

GH.typesetclab = function(term, cursorPosition) {
    var open_slug = GH.stringslug('{');
    var x_slug = GH.typeset(term[1], cursorPosition);
    var slash_slug = GH.stringslug('|');
    var ph_slug = GH.typeset(term[2], cursorPosition);
    var close_slug = GH.stringslug('}');
    var slugs = [open_slug, x_slug, slash_slug, ph_slug, close_slug];
    return GH.combineslugs(slugs, 9999);
};

GH.typesetInterval = function(term, cursorPosition) {
    var open_slug = GH.stringslug('{');
    var x_slug = GH.typeset(term[1], cursorPosition);
    var slash_slug = GH.stringslug('...');
    var ph_slug = GH.typeset(term[2], cursorPosition);
    var close_slug = GH.stringslug('}');
    var slugs = [open_slug, x_slug, slash_slug, ph_slug, close_slug];
    return GH.combineslugs(slugs, 9999);
};

GH.typesetsingleton = function(term, cursorPosition) {
    var open_slug = GH.stringslug('{');
    var A_slug = GH.typeset(term[1], cursorPosition);
    var close_slug = GH.stringslug('}');
    var slugs = [open_slug, A_slug, close_slug];
    return GH.combineslugs(slugs, 9999);
};

GH.typesetop = function(term, cursorPosition) {
    var open_slug = GH.stringslug('⟨');
    var x_slug = GH.typeset(term[1], cursorPosition);
    var comma_slug = GH.stringslug(',');
    var y_slug = GH.typeset(term[2], cursorPosition);
    var sp_slug = GH.spaceslug(1 + y_slug.prsp);
    var close_slug = GH.stringslug('⟩');
    var slugs = [open_slug, x_slug, comma_slug, sp_slug, y_slug, close_slug];
    return GH.combineslugs(slugs, 9999);
};

GH.typesetexp = function(term, prec, cursorPosition) {
    var x_slug = GH.typeset(term[1], cursorPosition);
    if (prec >= x_slug.prec) {
        x_slug = GH.parenthesize(x_slug);
    }
    var sup_slug = GH.stringslug('<sup>');
    var y_slug = GH.typeset(term[2], cursorPosition);
    var endsup_slug = GH.stringslug('</sup>');
    var slugs = [x_slug, sup_slug, y_slug, endsup_slug];
    return GH.combineslugs(slugs, GH.min(prec, x_slug.prec));
};

GH.isSetInExpectedForm = function(sexp) {
	return (sexp[0] == '{}') ||
           ((sexp[0] == 'u.') && (sexp[1][0] == '{}') && GH.isSetInExpectedForm(sexp[2]));
};

GH.getSetElements = function(set, result) {
	if (set[0] == '{}'){
		result.push(set[1]);
		return result;
	} else {
		result.push(set[1][1]);
		return GH.getSetElements(set[2], result);
	}
};

GH.typesetSet = function(term, cursorPosition) {
	var slugs = [GH.stringslug('{')];
	var elements = GH.getSetElements(term, []);
	for (var i = 0; i < elements.length; i++) {
		slugs.push(GH.typeset(elements[i], cursorPosition));
		if (i < elements.length - 1) {
		    slugs.push(GH.stringslug(','));
		}
	}
    slugs.push(GH.stringslug('}'));
    return GH.combineslugs(slugs, 9999);
};

GH.typeset = function(sexp, cursorPosition) {
	var str;
	var decimal = GH.numUtil.decimalNumber(sexp);
    if (GH.typeOf(sexp) == 'string') {
        var trans = { et: 'η',
            th: 'θ',
            ta: 'τ',
            ph: 'φ',
            ch: 'χ',
            ps: 'ψ'};
        if (sexp in trans) {
			str = GH.highlightSymbol(trans[sexp], sexp, cursorPosition);
        } else {
			str = GH.highlightSymbol(GH.escapeHtml(sexp), sexp, cursorPosition);
        }
        return GH.stringslug(str);
    } else if (!isNaN(decimal)) {
		str = GH.highlightSymbol(decimal.toString(), sexp, cursorPosition);
		return GH.stringslug(str, cursorPosition);
    } else if (sexp[0] == 'T') {
        return GH.stringslug('T', cursorPosition);
    } else if (sexp[0] == 'F') {
        return GH.stringslug('F', cursorPosition);
    } else if (sexp[0] == 'table') {
        return GH.typesettable(sexp, cursorPosition);
    } else if (sexp[0] == 'htmlSpan') {
        return GH.typesetHtmlSpan(sexp, cursorPosition);
    } else if (sexp[0] == '+') {
		// TODO: Finish highlighting the other symbols.
        return GH.typesetinfix(sexp, 'l', 2200, '+', cursorPosition);
    } else if (sexp[0] == '*' || sexp[0] == '∙') {
        return GH.typesetinfix(sexp, 'l', 2300, '∙', cursorPosition);
    } else if (sexp[0] == 'S') {
        return GH.typesetpostfix(sexp, 9999, '′', cursorPosition);
    } else if (sexp[0] == '=') {
        return GH.typesetinfix(sexp, 'n', 1050, '=', cursorPosition);
    } else if (sexp[0] == '=_') {
        // Note: at present, this isn't distinguished visually in any way
        // from '='. We should probably do something, like subtle color.
        return GH.typesetinfix(sexp, 'n', 1050, '=', cursorPosition);
    } else if (sexp[0] == '<=' || sexp[0] == '≤') {
        return GH.typesetinfix(sexp, 'n', 1050, '≤', cursorPosition);
    } else if (sexp[0] == '<') {
        return GH.typesetinfix(sexp, 'n', 1050, '&lt;', cursorPosition);
    } else if (sexp[0] == '|') {
        return GH.typesetinfix(sexp, 'n', 1050, '|', cursorPosition);
    } else if (sexp[0] == '->' || sexp[0] == '→') {
        return GH.typesetinfix(sexp, 'r', 250, '→', cursorPosition);
    } else if (sexp[0] == '<->' || sexp[0] == '↔') {
        return GH.typesetinfix(sexp, 'n', 100, '↔', cursorPosition);
    } else if (sexp[0] == '-.' || sexp[0] == '¬') {
        if (GH.typeOf(sexp[1]) != 'string') {
            if (sexp[1][0] == '=') {
                return GH.typesetinfix(sexp[1], 'n', 1050, '≠', cursorPosition);
            } else if (sexp[1][0] == '=_') {
                return GH.typesetinfix(sexp[1], 'n', 1050, '≠', cursorPosition);
            } else if (sexp[1][0] == '<=') {
                return GH.typesetinfix(sexp[1], 'n', 1050, '>', cursorPosition);
            } else if (sexp[1][0] == '<') {
                return GH.typesetinfix(sexp[1], 'n', 1050, '≥', cursorPosition);
            } else if (sexp[1][0] == 'e.' || sexp[1][0] == '∈') {
                return GH.typesetinfix(sexp[1], 'n', 1050, '∉', cursorPosition);
            } else if (sexp[1][0] == 'C_' || sexp[1][0] == '⊆') {
                return GH.typesetinfix(sexp[1], 'n', 1050, '⊈', cursorPosition);
            } else if (sexp[1][0] == 'E.' || sexp[1][0] == '∃') {
				return GH.typesetbinder(sexp[1], 40, '&#8708', cursorPosition);
			} else if (sexp[1][0] == 'C.' || sexp[1][0] == '⊂') {
                return GH.typesetinfix(sexp[1], 'n', 1050, '⊄', cursorPosition);
            }
        }
        return GH.typesetunary(sexp, 1000, '¬', cursorPosition);  // TODO: 2000?
    } else if (sexp[0] == '/\\' || sexp[0] == '∧') {
        return GH.typesetinfix(sexp, 'r', 400, '∧', cursorPosition);
    } else if (sexp[0] == '\\/' || sexp[0] == '∨') {
        return GH.typesetinfix(sexp, 'r', 300, '∨', cursorPosition);
    } else if (sexp[0] == 'A.' || sexp[0] == '∀') {
        return GH.typesetbinder(sexp, 40, '∀', cursorPosition);
    } else if (sexp[0] == 'E.' || sexp[0] == '∃') {
        return GH.typesetbinder(sexp, 40, '∃', cursorPosition);
    } else if (sexp[0] == 'E!' || sexp[0] == '∃!') {
        return GH.typesetbinder(sexp, 40, '∃!');
    } else if (sexp[0] == 'E*' || sexp[0] == '∃*') {
        return GH.typesetbinder(sexp, 40, '∃*', cursorPosition);
    } else if (sexp[0] == 'lambda' || sexp[0] == 'λ') {
        return GH.typesetbinder(sexp, 40, 'λ', cursorPosition);
    } else if (sexp[0] == '[/]') {
        return GH.typesetsubst(sexp, 40, cursorPosition);
    } else if (sexp[0] == '{|}') {
        return GH.typesetclab(sexp, cursorPosition);
    } else if (sexp[0] == '{...}') {
        return GH.typesetInterval(sexp, cursorPosition);
    } else if (sexp[0] == '{}') {
        return GH.typesetsingleton(sexp, cursorPosition);
    } else if (sexp[0] == 'e.' || sexp[0] == '∈') {
        return GH.typesetinfix(sexp, 'n', 1050, '∈', cursorPosition);
    } else if (sexp[0] == 'C_' || sexp[0] == '⊆') {
        return GH.typesetinfix(sexp, 'n', 1050, '⊆', cursorPosition);
    } else if (sexp[0] == 'C.' || sexp[0] == '⊂') {
        return GH.typesetinfix(sexp, 'n', 1050, '⊂', cursorPosition);
    } else if (GH.isSetInExpectedForm(sexp)) {
        return GH.typesetSet(sexp, cursorPosition);
	} else if (sexp[0] == 'i^i') {
        return GH.typesetinfix(sexp, 'r', 3500, '∩', cursorPosition);
    } else if (sexp[0] == 'u.') {
        return GH.typesetinfix(sexp, 'r', 3500, '∪', cursorPosition);
    } else if (sexp[0] == '{/}') {
        return GH.stringslug('∅', cursorPosition);
    } else if (sexp[0] == '<,>') {
        return GH.typesetop(sexp, cursorPosition);
    } else if (sexp[0] == 'exp') {
        return GH.typesetexp(sexp, 2500, cursorPosition);
    } else if (sexp[0] == 'mod') {
        return GH.typesetinfix(sexp, 'n', 2500, ' mod ', cursorPosition);
    } else if (sexp[0] == 'div') {
        return GH.typesetinfix(sexp, 'n', 2500, '&divide', cursorPosition);
    } else {
        var slugs = [GH.stringslug('('), GH.stringslug(GH.escapeHtml(sexp[0]))];
        for (var i = 1; i < sexp.length; i++) {
            slugs.push(GH.stringslug(' '));
            slugs.push(GH.typeset(sexp[i], cursorPosition));
        }
        slugs.push(GH.stringslug(')'));
        return GH.combineslugs(slugs, 9999);
    } 
};
