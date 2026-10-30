# A utility that splits the raw output of mm_xlat.py into modules suitable
# for checking into the ghilbert darcs repo

import sys, array

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

def format_sexp_rec(sexp, buf):
    if type(sexp) == type('atom'):
        buf.fromstring(sexp)
    else:
        buf.fromstring('(')
        for i in range(len(sexp)):
            format_sexp_rec(sexp[i], buf)
            if i < len(sexp) - 1: buf.fromstring(' ')
        buf.fromstring(')')

def format_sexp(sexp):
    buf = array.array('c')
    format_sexp_rec(sexp, buf)
    return buf.tostring()

def thm_to_stmt(line):
    line = line.replace('(', ' ( ')
    line = line.replace(')', ' ) ')
    ltoks = line.split()
    (name, dvs, hyps, concl, proof) =  parse_sexp(ltoks, 1)[1]
    hyps = [hyp[1] for hyp in hyps]
    return 'stmt ' + format_sexp([name, dvs, hyps, concl])

if __name__ == '__main__':
    set_mm_ax_ghi = file('zfc/set_mm_ax.ghi', 'w')
    set_mm_ghi = file('zfc/set_mm.ghi', 'w')
    set_mm_gh = file('zfc/set_mm.gh', 'w')

    hdr = '# Autoconverted from set.mm by xlat_mm.py and gen_set_mm.py'
    print >> set_mm_ax_ghi, hdr
    print >> set_mm_ax_ghi, 'param (PROP pax/prop () "")'

    print >> set_mm_ghi, hdr
    print >> set_mm_ghi, 'param (PROP pax/prop () "")'
    print >> set_mm_ghi, 'param (SET_MM_AX zfc/set_mm_ax (PROP) "")'

    print >> set_mm_gh, hdr
    print >> set_mm_gh, 'import (PROP pax/prop () "")'
    print >> set_mm_gh, 'import (SET_MM_AX zfc/set_mm_ax (PROP) "")'

    for line in sys.stdin.xreadlines():
        line = line.rstrip('\r\n')
        if line == '' or line[0] == '#':
            # banner at head of file
            print >> set_mm_ax_ghi, line
            print >> set_mm_ghi, line
            print >> set_mm_gh, line
        else:
            cmd = line.split()[0]
            if cmd == 'kind':
                if line != 'kind (wff)':
                    print >> set_mm_ax_ghi, line
            elif cmd == 'var':
                print >> set_mm_ax_ghi, line
                print >> set_mm_ghi, line
                print >> set_mm_gh, line
            elif cmd == 'term':
                termname = line.split()[2][1:]
                if termname not in ('-.', '->', '<->', '\\/', '/\\',
                                    '\\/\\/', '/\\/\\'):
                    print >> set_mm_ax_ghi, line
            elif cmd == 'thm':
                print >> set_mm_gh, line
                print >> set_mm_ghi, thm_to_stmt(line)
            elif cmd == 'stmt':
                stmtname = line.split()[1][1:]
                if stmtname not in ('ax-1', 'ax-2', 'ax-3', 'ax-mp',
                                    'df-bi', 'df-or', 'df-an',
                                    'df-3or', 'df-3an'):
                    print >> set_mm_ax_ghi, line
            else:
                print line
    print >> set_mm_gh, 'export (SET_MM zfc/set_mm (PROP SET_MM_AX) "")'

