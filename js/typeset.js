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

GH.sexptounicode = GH.sexptohtml; // TODO: get rid of

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

GH.typesetinfix = function(term, assoc, prec, op) {
    var lprsp = 0;
    var rprsp = 0;
    var left_slug = GH.typeset(term[1]);
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
    var right_slug = GH.typeset(term[2]);
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

GH.typesetclab = function(term) {
    var open_slug = GH.stringslug('{');
    var x_slug = GH.typeset(term[1]);
    var slash_slug = GH.stringslug('|');
    var ph_slug = GH.typeset(term[2]);
    var close_slug = GH.stringslug('}');
    var slugs = [open_slug, x_slug, slash_slug, ph_slug, close_slug];
    return GH.combineslugs(slugs, 9999);
};

GH.typesetsingleton = function(term) {
    var open_slug = GH.stringslug('{');
    var A_slug = GH.typeset(term[1]);
    var close_slug = GH.stringslug('}');
    var slugs = [open_slug, A_slug, close_slug];
    return GH.combineslugs(slugs, 9999);
};

GH.typesetop = function(term) {
    var open_slug = GH.stringslug('\u27e8');
    var x_slug = GH.typeset(term[1]);
    var comma_slug = GH.stringslug(',');
    var y_slug = GH.typeset(term[2]);
    var sp_slug = GH.spaceslug(1 + y_slug.prsp);
    var close_slug = GH.stringslug('\u27e9');
    var slugs = [open_slug, x_slug, comma_slug, sp_slug, y_slug, close_slug];
    return GH.combineslugs(slugs, 9999);
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

GH.typeset = function(sexp) {
    if (GH.typeOf(sexp) == 'string') {
        var trans = { et: '\u03b7',
            th: '\u03b8',
            ta: '\u03c4',
            ph: '\u03c6',
            ch: '\u03c7',
            ps: '\u03c8'};
        if (sexp in trans) {
            return GH.stringslug(trans[sexp]);
        } else {
            return GH.stringslug(GH.escapeHtml(sexp));
        }
    } else if (sexp[0] == '0') {
        return GH.stringslug('0');
    } else if (sexp[0] == '1') {
        return GH.stringslug('1');
    } else if (sexp[0] == '+') {
        return GH.typesetinfix(sexp, 'l', 2200, '+');
    } else if (sexp[0] == '*') {
        return GH.typesetinfix(sexp, 'l', 2300, '\u2219');
    } else if (sexp[0] == 'S') {
        return GH.typesetpostfix(sexp, 9999, '\u2032');
    } else if (sexp[0] == '=') {
        return GH.typesetinfix(sexp, 'n', 1050, '=');
    } else if (sexp[0] == '=_') {
        // Note: at present, this isn't distinguished visually in any way
        // from '='. We should probably do something, like subtle color.
        return GH.typesetinfix(sexp, 'n', 1050, '=');
    } else if (sexp[0] == '<=') {
        return GH.typesetinfix(sexp, 'n', 1050, '\u2264');
    } else if (sexp[0] == '<') {
        return GH.typesetinfix(sexp, 'n', 1050, '&lt;');
    } else if (sexp[0] == '|') {
        return GH.typesetinfix(sexp, 'n', 1050, '|');
    } else if (sexp[0] == '->') {
        return GH.typesetinfix(sexp, 'r', 250, '\u2192');
    } else if (sexp[0] == '<->') {
        return GH.typesetinfix(sexp, 'n', 100, '\u2194');
    } else if (sexp[0] == '-.') {
        if (GH.typeOf(sexp[1]) != 'string') {
            if (sexp[1][0] == '=') {
                return GH.typesetinfix(sexp[1], 'n', 1050, '\u2260');
            } else if (sexp[1][0] == '=_') {
                return GH.typesetinfix(sexp[1], 'n', 1050, '\u2260');
            } else if (sexp[1][0] == 'e.') {
                return GH.typesetinfix(sexp[1], 'n', 1050, '\u2209');
            } else if (sexp[1][0] == 'C_') {
                return GH.typesetinfix(sexp[1], 'n', 1050, '\u2288');
            } else if (sexp[1][0] == 'C.') {
                return GH.typesetinfix(sexp[1], 'n', 1050, '\u2284');
            }
        }
        return GH.typesetunary(sexp, 1000, '\u00ac');  // TODO: 2000?
    } else if (sexp[0] == '/\\') {
        return GH.typesetinfix(sexp, 'r', 400, '\u2227');
    } else if (sexp[0] == '\\/') {
        return GH.typesetinfix(sexp, 'r', 300, '\u2228');
    } else if (sexp[0] == 'A.') {
        return GH.typesetbinder(sexp, 40, '\u2200');
    } else if (sexp[0] == 'E.') {
        return GH.typesetbinder(sexp, 40, '\u2203');
    } else if (sexp[0] == 'E!') {
        return GH.typesetbinder(sexp, 40, '\u2203!');
    } else if (sexp[0] == 'E*') {
        return GH.typesetbinder(sexp, 40, '\u2203*');
    } else if (sexp[0] == 'lambda') {
        return GH.typesetbinder(sexp, 40, '\u03bb');
    } else if (sexp[0] == '[/]') {
        return GH.typesetsubst(sexp, 40);
    } else if (sexp[0] == '{|}') {
        return GH.typesetclab(sexp);
    } else if (sexp[0] == '{}') {
        return GH.typesetsingleton(sexp);
    } else if (sexp[0] == 'e.') {
        return GH.typesetinfix(sexp, 'n', 1050, '\u2208');
    } else if (sexp[0] == 'C_') {
        return GH.typesetinfix(sexp, 'n', 1050, '\u2286');
    } else if (sexp[0] == 'C.') {
        return GH.typesetinfix(sexp, 'n', 1050, '\u2282');
    } else if (sexp[0] == 'i^i') {
        return GH.typesetinfix(sexp, 'n', 3500, '\u2229');
    } else if (sexp[0] == 'u.') {
        return GH.typesetinfix(sexp, 'n', 3500, '\u222a');
    } else if (sexp[0] == '<,>') {
        return GH.typesetop(sexp);
    } else if (sexp[0] == 'exp') {
        return GH.typesetexp(sexp, 2500);
    } else {
        var slugs = [GH.stringslug('('), GH.stringslug(sexp[0])];
        for (var i = 1; i < sexp.length; i++) {
            slugs.push(GH.stringslug(' '));
            slugs.push(GH.typeset(GH.escapeHtml(sexp[i])));
        }
        slugs.push(GH.stringslug(')'));
        return GH.combineslugs(slugs, 9999);
    } 
};
