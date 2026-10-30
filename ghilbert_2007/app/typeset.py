# Utilities for typesetting Ghilbert terms

import sys, array, verify

widlim = 400

def parse_sexp(toks, i):
    if toks[i] == '(':
        list = []
        i += 1
        while 1:
            if toks[i] == ')':
                break
            (i, el) = parse_sexp(toks, i)
            list.append(el)
        i += 1
        return (i, list)
    else:
        return (i + 1, toks[i])

class ReadCmds:
    def __init__(self, s):
        self.s = s
        self.lineno = 0
    def read(self):
        balance = 0
        toks = []
        while len(toks) == 0 or balance > 0:
            line = self.s.readline()
            self.lineno += 1
            if line == '':
                if balance > 0:
                    raise SyntaxError('unbalanced parens at EOF')
                return None
            line = line.split('#')[0]
            line = line.replace('(', ' ( ')
            line = line.replace(')', ' ) ')
            ltoks = line.split()
            if len(ltoks) >= 0:
                toks.extend(ltoks)
                balance += reduce(lambda x, y: x + y,
                                  map(lambda x: {'(': 1, ')': -1}.get(x, 0),
                                      ltoks), 0)
        return toks


def ps_mkstring(text):
    buf = array.array('c')
    buf.fromstring('(')
    for i in range(len(text)):
        c = ord(text[i])
        if c >= 32 and c < 127 and c not in (ord('('), ord(')'), ord('\\')):
            buf.fromstring(chr(c))
        else:
            buf.fromstring('\\%03o' % ord(text[i]))
    buf.fromstring(')')
    return buf.tostring()

class Page:
    def __init__(self, out):
        self.out = out
        self.x0 = 36
        self.x = self.x0
        self.y = 750
        self.curptvalid = 0
        print >> out, '%!PS-Adobe'
    def read_font(self, fontname, font_fn):
        fontf = file(font_fn)
        while 1:
            line = fontf.readline()
            if line == '':
                break
            self.out.write(line)
    def write_string(self, alias, fontsize, text):
        fontname = fonttab[alias]
        print >> self.out, '/%s %s selectfont' % (fontname, fontsize)
        if not self.curptvalid:
            print >> self.out, '%g %g moveto' % (self.x, self.y)
            self.curptvalid = 1
        print >> self.out, ps_mkstring(text) + ' show'
    def write_sexp(self, sexp):
        if sexp[0] == 'glyph':
            self.write_string(sexp[1], sexp[2], chr(int(sexp[3])))
        elif sexp[0] == 'sp':
            self.space(int(sexp[1]))
        elif sexp[0] == 'hbox':
            for child in sexp[1:]:
                self.write_sexp(child)
        elif sexp[0] == 'vbox':
            self.write_vbox(sexp)
        elif sexp[0] == 'hline':
            print >> self.out, 'gsave .5 setlinewidth %g 0 rlineto stroke grestore' % int(sexp[1])
        elif sexp[0] == 'rise':
            print >> self.out, '0 %g rmoveto' % int(sexp[1])
            for child in sexp[2:]:
                self.write_sexp(child)
            print >> self.out, '0 %g rmoveto' % -int(sexp[1])
        elif sexp[0] == 'string':
            self.write_string(sexp[1], sexp[2], sexp[3])
        else:
            raise RuntimeError('unknown sexp ' + `sexp`)
    def space(self, sp):
        print >> self.out, '%g 0 rmoveto' % sp
    def write_vbox(self, sexp):
        for i in range(1, len(sexp) - 1, 2):
            print >> self.out, 'gsave'
            self.write_sexp(sexp[i])
            print >> self.out, 'grestore 0 %g rmoveto' % -int(sexp[i + 1])
        self.write_sexp(sexp[-1])
    def write_slug_nl(self, slug):
        if (self.y - slug.height < 22):
            print >> self.out, 'showpage'
            self.y = 750
        self.write_sexp(slug.markup)
        self.y -= slug.height
        self.curptvalid = 0
    def close(self):
        print >> self.out, 'showpage'

# A fragment of term, converted to PS
class Slug:
    def __init__(self, prec, width, nlines, markup, prsp = 0, height = 14):
        self.prec = prec
        self.width = width
        self.nlines = nlines
        self.height = height
        #self.ascent = 11
        self.markup = markup
        self.prsp = prsp

def markup_slug(markup):
    # todo: measure width
    return Slug(9999, 5, 1, markup)

def string_slug(font, size, str):
    return Slug(9999, 5 * len(str), 1, ['string', font, size, str])

def space_slug(wid):
    return Slug(9999, wid, 1, ['sp', wid])

def hline_slug(wid):
    return Slug(9999, wid, 1, ['rise', '10', ['hline', wid]], -1, 1)

def combine_slugs(slugs, prec, prsp = 0):
    width = 0
    height = 0
    markup = ['hbox']
    nlines = 1
    for slug in slugs:
        width += slug.width
        height = max(height, slug.height)
        #if slug.nlines != 1:
        #    markup.append(['string', 'CMR10', '10', '[%d]' % slug.nlines])
        nlines += slug.nlines - 1
        markup.append(slug.markup)
    return Slug(prec, width, nlines, markup, prsp, height)

def vbox_slugs(slugs, prec, prsp = 0):
    width = 0
    height = 0
    markup = ['vbox']
    nlines = 0
    for slug in slugs:
        width = slug.width
        height += slug.height
        nlines += slug.nlines
        markup.append(slug.markup)
        markup.append(slug.height)
    del markup[-1]
    return Slug(prec, width, nlines, markup, prsp, height)

def combine_infix_slugs(slugs, prec, prsp):
    result = combine_slugs(slugs, prec, prsp)
    if (result.width > widlim or result.nlines > 1):
        inner = []
        for i in range(0, len(slugs) - 1, 4):
            if i:
                inslugs = [space_slug(10)]
            else:
                inslugs = []
            inslugs.extend(slugs[i: i + 3])
            inner.append(combine_slugs(inslugs, prec))
        inner.append(combine_slugs([space_slug(10), slugs[-1]], prec))
        result = vbox_slugs(inner, prec, prsp)
    return result

def parenthesize(slug):
    lparen_slug = markup_slug(['glyph', 'CMR10', '10', '40'])
    rparen_slug = markup_slug(['glyph', 'CMR10', '10', '41'])
    return combine_slugs([lparen_slug, slug, rparen_slug], 9999)

kindtab = {}

def default_set_term(term):
    #print 'dst:', term
    if type(term) == type(''):
        return string_slug('Sans', '10', term)
    elif type(term) == type([]):
        sig = vg.terms[term[0]]
        argkinds = sig[2]
        if termtab.has_key(term[0]):
            prod = termtab[term[0]]
            if prod[0] == 'infix':
                assoc = prod[1]
                prec = int(prod[2])
                left_slug = set_term(term[1], argkinds[0])
                lprec = left_slug.prec
                if assoc == 'l':
                    lprec += 1
                if prec >= lprec:
                    left_slug = parenthesize(left_slug)
                    lprsp = 3
                elif prec + 1 == lprec:
                    lprsp = left_slug.prsp
                else:
                    lprsp = left_slug.prsp + 2
                op_slug = markup_slug(prod[3])
                right_slug = set_term(term[2], argkinds[1])
                rprec = right_slug.prec
                if assoc == 'r':
                    rprec += 1
                if prec >= rprec:
                    right_slug = parenthesize(right_slug)
                    rprsp = 3
                elif prec + 1 == rprec:
                    rprsp = right_slug.prsp
                else:
                    rprsp = right_slug.prsp + 2
                prsp = max(lprsp, op_slug.prsp, rprsp)
                sp = max(0, prsp - 1)
                sp_slug = space_slug(sp)
                slugs = [left_slug, sp_slug, op_slug, sp_slug, right_slug]
                return combine_infix_slugs(slugs, prec, prsp)
            elif prod[0] == 'ternary':
                assoc = prod[1]
                prec = int(prod[2])
                left_slug = set_term(term[1], argkinds[0])
                lprec = left_slug.prec
                if assoc == 'l':
                    lprec += 1
                if prec >= lprec:
                    left_slug = parenthesize(left_slug)
                    lprsp = 3
                elif prec + 1 == lprec:
                    lprsp = left_slug.prsp
                else:
                    lprsp = left_slug.prsp + 2
                op1_slug = markup_slug(prod[3])
                mid_slug = set_term(term[2], argkinds[1])
                mprec = mid_slug.prec
                if prec >= mprec:
                    mid_slug = parenthesize(mid_slug)
                    mprsp = 3
                elif prec + 1 == mprec:
                    mprsp = mid_slug.prsp
                else:
                    mprsp = mid_slug.prsp + 2
                op2_slug = markup_slug(prod[4])
                right_slug = set_term(term[3], argkinds[2])
                rprec = right_slug.prec
                if assoc == 'r':
                    rprec += 1
                if prec >= rprec:
                    right_slug = parenthesize(right_slug)
                    rprsp = 3
                elif prec + 1 == rprec:
                    rprsp = right_slug.prsp
                else:
                    rprsp = right_slug.prsp + 2
                prsp = max(lprsp, op1_slug.prsp, mprsp, op2_slug.prsp, rprsp)
                sp = max(0, prsp - 1)
                sp_slug = space_slug(sp)
                slugs = [left_slug, sp_slug, op1_slug, sp_slug, mid_slug, sp_slug, op2_slug, sp_slug, right_slug]
                return combine_infix_slugs(slugs, prec, prsp)
            elif prod[0] == 'unary':
                prec = int(prod[1])
                op_slug = markup_slug(prod[2])
                right_slug = set_term(term[1], argkinds[0])
                if prec > right_slug.prec:
                    right_slug = parenthesize(right_slug)
                sp_slug = space_slug(right_slug.prsp)
                slugs = [op_slug, sp_slug, right_slug]
                return combine_slugs(slugs, prec, 1)
            elif prod[0] == 'binder':
                prec = int(prod[1])
                op_slug = markup_slug(prod[2])
                var_slug = set_term(term[1], argkinds[0])
                body_slug = set_term(term[2], argkinds[1])
                sp_slug = space_slug(1 + body_slug.prsp)
                slugs = [op_slug, var_slug, sp_slug, body_slug]
                return combine_slugs(slugs, prec)
            elif prod[0] == 'qbinder':
                prec = int(prod[1])
                op_slug = markup_slug(prod[2])
                var_slug = set_term(term[1], argkinds[0])
                qual_slug = markup_slug(prod[3])
                qarg_slug = set_term(term[2], argkinds[1])
                body_slug = set_term(term[3], argkinds[2])
                prsp = max(qarg_slug.prsp, body_slug.prsp)
                sp_slug = space_slug(2 + prsp)
                slugs = [op_slug, var_slug, qual_slug, qarg_slug, sp_slug, body_slug]
                if prec > 1000:
                    # for indexed union and intersection
                    new_prsp = prsp + 4
                else:
                    # for quantifiers
                    new_prsp = 0
                return combine_slugs(slugs, prec, new_prsp)
            elif prod[0] == 'quo':
                prec = int(prod[1])
                lbrac_slug = markup_slug(prod[2])
                left_slug = set_term(term[1], argkinds[0])
                rbrac_slug = markup_slug(prod[3])
                right_slug = set_term(term[2], argkinds[1])
                slugs = [lbrac_slug, left_slug, rbrac_slug, right_slug]
                return combine_slugs(slugs, prec, right_slug.prsp + 2)
            elif prod[0] == 'sn':
                prec = int(prod[1])
                lbrac_slug = markup_slug(prod[2])
                left_slug = set_term(term[1], argkinds[0])
                rbrac_slug = markup_slug(prod[3])
                slugs = [lbrac_slug, left_slug, rbrac_slug]
                return combine_slugs(slugs, prec)
            elif prod[0] == 'compr':
                prec = int(prod[1])
                lbrac_slug = markup_slug(prod[2])
                left_slug = set_term(term[1], argkinds[0])
                op_slug = markup_slug(prod[3])
                right_slug = set_term(term[2], argkinds[1])
                rbrac_slug = markup_slug(prod[4])
                slugs = [lbrac_slug, left_slug, op_slug, right_slug, rbrac_slug]
                return combine_slugs(slugs, prec)
            elif prod[0] == 'compr3':
                prec = int(prod[1])
                lbrac_slug = markup_slug(prod[2])
                left_slug = set_term(term[1], argkinds[0])
                op1_slug = markup_slug(prod[3])
                mid_slug = set_term(term[2], argkinds[1])
                op2_slug = markup_slug(prod[4])
                right_slug = set_term(term[3], argkinds[2])
                rbrac_slug = markup_slug(prod[5])
                slugs = [lbrac_slug, left_slug, op1_slug, mid_slug, op2_slug, right_slug, rbrac_slug]
                return combine_slugs(slugs, prec)
            elif prod[0] == 'compr4':
                prec = int(prod[1])
                lbrac_slug = markup_slug(prod[2])
                left_slug = set_term(term[1], argkinds[0])
                op1_slug = markup_slug(prod[3])
                mid1_slug = set_term(term[2], argkinds[1])
                op2_slug = markup_slug(prod[4])
                mid2_slug = set_term(term[3], argkinds[2])
                op3_slug = markup_slug(prod[5])
                right_slug = set_term(term[4], argkinds[3])
                rbrac_slug = markup_slug(prod[6])
                slugs = [lbrac_slug, left_slug, op1_slug, mid1_slug, op2_slug, mid2_slug, op3_slug, right_slug, rbrac_slug]
                return combine_slugs(slugs, prec)
            elif prod[0] == 'subst':
                prec = int(prod[1])
                lbrac_slug = markup_slug(prod[2])
                left_slug = set_term(term[1], argkinds[0])
                op_slug = markup_slug(prod[3])
                right_slug = set_term(term[2], argkinds[1])
                rbrac_slug = markup_slug(prod[4])
                body_slug = set_term(term[3], argkinds[2])
                if prec > body_slug.prec:
                    body_slug = parenthesize(body_slug)
                    prsp = 1
                else:
                    prsp = right_slug.prsp
                slugs = [lbrac_slug, left_slug, op_slug, right_slug, rbrac_slug, body_slug]
                return combine_slugs(slugs, prec, prsp + 2)
            elif prod[0] == 'const':
                slug = markup_slug(prod[1])
                return slug
        else:
            slugs = [string_slug('Sans', '10', term[0])]
            for i in range(1, len(term)):
                # maybe make space depend on prsp
                slugs.append(space_slug(3))
                slugs.append(set_term(term[i], argkinds[i - 1]))
            combined = combine_slugs(slugs, 9999)
            if combined.width > widlim or combined.nlines > 1:
                inner = [combine_slugs(slugs[0:min(3, len(slugs))], -1)]
                for i in range(3, len(slugs), 2):
                    inner.append(combine_slugs([space_slug(10), slugs[i + 1]], -1))
                combined = vbox_slugs(inner, 9999)
            return parenthesize(combined)

def set_wff(term):
    if type(term) == type('var'):
        if vartab.has_key(term):
            markup = vartab[term]
            return markup_slug(markup)
    elif type(term) == type([]):
        if term[0] == 'br':
            slug = set_br(term)
            if slug: return slug
            left_slug = set_term(term[1], 'class')
            op_slug = set_term(term[2], 'class')
            right_slug = set_term(term[3], 'class')
            prec = 1050
            lprec = left_slug.prec
            if prec >= lprec:
                left_slug = parenthesize(left_slug)
                lprsp = 3
            elif prec + 1 == lprec:
                lprsp = left_slug.prsp
            else:
                lprsp = left_slug.prsp + 2
            if 4500 >= op_slug.prec:
                op_slug = parenthesize(op_slug)
                oprsp = 3
            else:
                oprsp = op_slug.prsp
            rprec = right_slug.prec
            if prec >= rprec:
                right_slug = parenthesize(right_slug)
                rprsp = 3
            elif prec + 1 == rprec:
                rprsp = right_slug.prsp
            else:
                rprsp = right_slug.prsp + 2
            prsp = max(lprsp, oprsp, rprsp)
            sp = max(0, prsp - 1)
            sp_slug = space_slug(sp)
            slugs = [left_slug, sp_slug, op_slug, sp_slug, right_slug]
            return combine_infix_slugs(slugs, prec, prsp)

def set_set(term):
    return string_slug('CMMI10', '10', term)

def set_class(term):
    if type(term) == type([]):
        if term[0] == 'cv':
            return set_term(term[1], 'set')
        if term[0] == '`':
            slug = set_fval(term)
            if slug: return slug
        elif term[0] == 'opr':
            slug = set_opr(term)
            if slug: return slug
            left_slug = set_term(term[1], 'class')
            op_slug = set_term(term[2], 'class')
            right_slug = set_term(term[3], 'class')
            prec = 0
            lprec = left_slug.prec
            if prec >= lprec:
                left_slug = parenthesize(left_slug)
                lprsp = 3
            elif prec + 1 == lprec:
                lprsp = left_slug.prsp
            else:
                lprsp = left_slug.prsp + 2
            if 4500 >= op_slug.prec:
                op_slug = parenthesize(op_slug)
                oprsp = 3
            else:
                oprsp = op_slug.prsp
            rprec = right_slug.prec
            if prec >= rprec:
                right_slug = parenthesize(right_slug)
                rprsp = 3
            elif prec + 1 == rprec:
                rprsp = right_slug.prsp
            else:
                rprsp = right_slug.prsp + 2
            prsp = max(lprsp, oprsp, rprsp)
            sp = max(0, prsp - 1)
            sp_slug = space_slug(sp)
            slugs = [left_slug, sp_slug, op_slug, sp_slug, right_slug]
            return combine_infix_slugs(slugs, prec, prsp)
        elif len(term) == 1 and oprtab.has_key(term[0]):
            prod = oprtab[term[0]]
            if prod[0] == 'infix':
                return markup_slug(prod[3])
        elif len(term) == 1 and brtab.has_key(term[0]):
            prod = brtab[term[0]]
            if prod[0] == 'infix':
                return markup_slug(prod[3])
    elif type(term) == type(''):
        return string_slug('CMMI10', '10', term)

def set_fval(term):
    left = term[1]
    if type(left) == type([]) and len(left) == 1 and fvaltab.has_key(left[0]):
        prod = fvaltab[left[0]]
        fvaltype = prod[0]
        prec = int(prod[1])
        body_slug = set_term(term[2], 'class')
        if prec > body_slug.prec:
            body_slug = parenthesize(body_slug)
        if fvaltype == 'brack':
            lbrac_slug = markup_slug(prod[2])
            rbrac_slug = markup_slug(prod[3])
            slugs = [lbrac_slug, body_slug, rbrac_slug]
            prec = int(prod[4])
            prsp = 1
        elif fvaltype == 'lunary':
            op_slug = markup_slug(prod[2])
            slugs = [op_slug, body_slug]
            prsp = 1
        elif fvaltype == 'runary':
            op_slug = markup_slug(prod[2])
            slugs = [body_slug, op_slug]
            prsp = 1
        return combine_slugs(slugs, prec, prsp)

def set_opr(term):
    op = term[2]
    if type(op) == type([]) and len(op) == 1 and oprtab.has_key(op[0]):
        prod = oprtab[op[0]]
        optype = prod[0]
        assoc = prod[1]
        prec = int(prod[2])
        left_slug = set_term(term[1], 'class')
        right_slug = set_term(term[3], 'class')
        if optype == 'infix':
            assoc = prod[1]
            prec = int(prod[2])
            op_slug = markup_slug(prod[3])
            lprec = left_slug.prec
            if assoc == 'l':
                lprec += 1
            if prec >= lprec:
                left_slug = parenthesize(left_slug)
                lprsp = 3
            elif prec + 1 == lprec:
                lprsp = left_slug.prsp
            else:
                lprsp = left_slug.prsp + 2
            rprec = right_slug.prec
            if assoc == 'r':
                rprec += 1
            if prec >= rprec:
                right_slug = parenthesize(right_slug)
                rprsp = 3
            elif prec + 1 == rprec:
                rprsp = right_slug.prsp
            else:
                rprsp = right_slug.prsp + 2
            prsp = max(lprsp, rprsp)
            sp = max(0, prsp - 1)
            sp_slug = space_slug(sp)
            slugs = [left_slug, sp_slug, op_slug, sp_slug, right_slug]
            return combine_infix_slugs(slugs, prec, prsp)

def set_br(term):
    op = term[2]
    if type(op) == type([]) and len(op) == 1 and brtab.has_key(op[0]):
        prod = brtab[op[0]]
        optype = prod[0]
        left_slug = set_term(term[1], 'class')
        right_slug = set_term(term[3], 'class')
        if optype == 'infix':
            assoc = prod[1]
            prec = int(prod[2])
            op_slug = markup_slug(prod[3])
            lprec = left_slug.prec
            if assoc == 'l':
                lprec += 1
            if prec >= lprec:
                left_slug = parenthesize(left_slug)
                lprsp = 3
            elif prec + 1 == lprec:
                lprsp = left_slug.prsp
            else:
                lprsp = left_slug.prsp + 2
            rprec = right_slug.prec
            if assoc == 'r':
                rprec += 1
            if prec >= rprec:
                right_slug = parenthesize(right_slug)
                rprsp = 3
            elif prec + 1 == rprec:
                rprsp = right_slug.prsp
            else:
                rprsp = right_slug.prsp + 2
            prsp = max(lprsp, rprsp)
            sp = max(0, prsp - 1)
            sp_slug = space_slug(sp)
            slugs = [left_slug, sp_slug, op_slug, sp_slug, right_slug]
            return combine_infix_slugs(slugs, prec, prsp)

def set_var(term):
    pass

def set_val(term):
    if type(term) == type('var'):
        if vartab.has_key(term):
            markup = vartab[term]
            return markup_slug(markup)
    elif term[0] == 'cv':
        return set_term(term[1], 'var')

def set_type(term):
    pass

kindtab['wff'] = set_wff
kindtab['set'] = set_set
kindtab['class'] = set_class

# for hol
kindtab['var'] = set_var
kindtab['val'] = set_val
kindtab['type'] = set_val

# for peano
kindtab['num'] = set_val

def set_term(term, prod):
    slug = kindtab[prod](term)
    if slug == None:
        slug = default_set_term(term)
    if slug == None:
        slug = markup_slug(['string', 'Sans', '10', '??'])
    return slug

def print_term(page, term, prod = 'wff'):
    slug = set_term(term, prod)
    page.write_slug_nl(slug)

def print_stmt(page, stmt):
    slugs = [string_slug('Sans', '10', stmt[0])]
    slugs.append(space_slug(10))
    if len(stmt[2]):
        for hyp in stmt[2]:
            slugs.append(set_term(hyp, 'wff'))
            slugs.append(space_slug(10))
        slugs.append(markup_slug(['glyph', 'CMSY10', '10', '41']))
        slugs.append(space_slug(10))
    slugs.append(set_term(stmt[3], 'wff'))
    combined = combine_slugs(slugs, -1)
    if combined.width > widlim or combined.nlines > 1:
        # vertical layout
        inner = []
        if len(stmt[2]):
            for hyp in stmt[2]:
                inner.append(set_term(hyp, 'wff'))
            inner.append(hline_slug(200))
        inner.append(set_term(stmt[3], 'wff'))
        slugs = [string_slug('Sans', '10', stmt[0])]
        slugs.append(space_slug(10))
        slugs.append(vbox_slugs(inner, -1))
        combined = combine_slugs(slugs, -1)
    page.write_slug_nl(combined)

def print_thm(page, thm):
    stmt = [thm[0], thm[1], [hyp for (label, hyp) in thm[2]], thm[3]]
    return print_stmt(page, stmt)

fonttab = {}
termtab = {}
vartab = {}
fvaltab = {}
oprtab = {}
brtab = {}

def read_script(page, sfile):
    script = ReadCmds(sfile)
    while 1:
        line = script.read()
        if line == None:
            break
	(i, args) = parse_sexp(line, 1)
	#print args
        if len(line) > 0:
            cmd = line[0]
            if cmd == 'font':
                fontname = args[0]
                font_fn = args[1]
                fonttab[args[2]] = fontname
                page.read_font(fontname, font_fn)
	    elif cmd == 'print':
                fontname = args[0]
                fontsize = args[1]
                text = args[2]
                page.write_string(fontname, fontsize, text)
	    elif cmd == 'glyph':
                fontname = args[0]
                fontsize = args[1]
                text = chr(int(args[2]))
                page.write_string(fontname, fontsize, text)
            elif cmd == 'var':
                vartab[args[0]] = args[1]
            elif cmd == 'term':
                termtab[args[0]] = args[1]
            elif cmd == 'fval':
                fvaltab[args[0]] = args[1]
            elif cmd == 'opr':
                oprtab[args[0]] = args[1]
            elif cmd == 'br':
                brtab[args[0]] = args[1]
            elif cmd == 'print_term':
                print_term(page, args)
            elif cmd == 'stmt':
                print_stmt(page, args)

def typeset_load_gh(page, fn, print_thms = True):
    global vg # probably objectify this
    sc = verify.Scanner(file(fn))
    vg = verify.VerifyGh()
    while 1:
        cmd = sc.get_tok()
        if cmd == None:
            break
        else:
            try:
                arg = verify.read_sexp(sc)
                if cmd == 'thm' and print_thms:
                    print_thm(page, arg)
                vg.do_cmd(cmd, arg)
            except verify.VerifyError, x:
                if x.label != None:
                    print 'Verification error at line', sc.lineno, 'in thm:', x.label
                else:
                    print 'Verification error at line', sc.lineno
                print x.args
                if x.step != None:
                    vg.print_step_context(x.step)
                if x.stack != None:
                    vg.print_stack(x.stack)
                return vg#False
    return vg

if __name__ == '__main__':
    verify.verbosity = 0
    script = file(sys.argv[1])
    page = Page(sys.stdout)
    read_script(page, script)

    if len(sys.argv) > 2:
        typeset_load_gh(page, sys.argv[2])
    page.close()
    
