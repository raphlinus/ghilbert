#!/usr/bin/env python

import x3
import verify
import display
import typeset

def do_save():
    savefn = savefnbase + '_' + pv.thmname + '.ghfrag'
    fo = file(savefn, 'w')
    for line in pv.buf:
        print >> fo, line
    print 'saved to', savefn

def do_quit():
    print 'close'
    # todo: actually close window, needs x3-side help

def my_callback(cmd, what, arg, more):
    if cmd == 'abou':
        popup_about()
    elif cmd == 'save':
        do_save()
    elif cmd == 'quit':
        do_quit()
    else:
        print cmd, what, arg

def abou_callback(cmd, what, arg, more):
    print 'abou:', cmd, what, arg
    
def popup_about():
    win = x3.window(0, "About Ghilbert", abou_callback)
    v = x3.vbox(x3.pad(win, 10, 10, 10, 10), 0, 12)
    x3.label(v, '''The prototype GUI Ghilbert client''')
    v.setpacking(False, False, 0)
    x3.button(v, 'ok', 'Ok')


def load_gh(fn):
    sc = verify.Scanner(file(fn))
    vg = verify.VerifyGh()
    while 1:
        cmd = sc.get_tok()
        if cmd == None:
            break
        else:
            try:
                arg = verify.read_sexp(sc)
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

def asciival(keyname, mods, code):
    if code >= 32 and code <= 127 and (mods & 0x4c) == 0:
        return chr(code)

# split string into tokens with ranges
def splitrange(str):
    result = []
    beg = 0
    for i in range(len(str)):
        c = str[i]
        if c == ' ':
            if i != beg:
                result.append((str[beg:i], beg, i))
            beg = i + 1
        elif c in '()':
            if i != beg:
                result.append((str[beg:i], beg, i))
            result.append((str[i:i+1], i, i+1))
            beg = i + 1
        elif c in '#':
            if i != beg:
                result.append((str[beg:i], beg, i))
            beg = len(str)
            break
    if beg != len(str):
        result.append((str[beg:], beg, len(str)))
    return result

class editview:
    def __init__(self):
        self.buf = ['']
        self.bgcolors = None
        self.cursor = (0, 0)
        self.x0 = 10
        self.y0 = 20
        self.linespace = 14
    def updated(self):
        pass
    def limcursor(self):
        col, row = self.cursor
        return (min(col, len(self.buf[row])), row)
    def move_cursor(self, col, row):
        if row >= 0 and row < len(self.buf) and col >= 0:
            self.cursor = (col, row)
            # There's no dc for the textextents - we really need a text
            # layer that can handle this, and for hit testing too
            #x = dc.textextents(self.buf[row][:col])[4]
            x = 0
            y = self.y0 + row * self.linespace
            self.view.scrollto(x, y - 11, 1, 14)
            self.view.dirty()
    def key(self, name, mods, code):
        if name == 'Right':
            col, row = self.limcursor()
            if col == len(self.buf[row]):
                if row < len(self.buf):
                    self.move_cursor(0, row + 1)
            else:
                self.move_cursor(col + 1, row)
            return 1
        elif name == 'Left':
            col, row = self.limcursor()
            if col == 0:
                self.move_cursor(len(self.buf[row - 1]), row - 1)
            else:
                self.move_cursor(col - 1, row)
            return 1
        elif name == 'Up':
            col, row = self.cursor
            self.move_cursor(col, row - 1)
            return 1
        elif name == 'Down':
            col, row = self.cursor
            self.move_cursor(col, row + 1)
            return 1
        elif name == 'Home':
            col, row = self.cursor
            self.move_cursor(0, row)
            return 1
        elif name == 'End':
            col, row = self.cursor
            self.move_cursor(len(self.buf[row]), row)
            return 1
        elif name == 'Return':
            col, row = self.limcursor()
            self.buf[row:row + 1] = [self.buf[row][:col], self.buf[row][col:]]
            self.move_cursor(0, row + 1)
            self.updated()
            return 1
        elif name == 'BackSpace':
            col, row = self.limcursor()
            if col > 0:
                self.buf[row] = self.buf[row][:col - 1] + self.buf[row][col:]
                self.move_cursor(col - 1, row)
            elif row > 0:
                self.move_cursor(len(self.buf[row - 1]), row - 1)
                self.buf[row - 1: row + 1] = [self.buf[row - 1] + self.buf[row]]
            self.updated()
            return 1
        else:
            c = asciival(name, mods, code)
            if c:
                col, row = self.limcursor()
                self.buf[row] = self.buf[row][:col] + c + self.buf[row][col:]
                self.move_cursor(col + 1, row)
                self.updated()
                return 1
            else:
                print 'Unhandled key:', name, mods, code
        return 0
    def draw(self, dc):
        dc.setrgba(1, 1, 1, 1)
        dc.rectangle(*dc.rect)
        dc.fill()
        x0 = self.x0
        y = self.y0
        dc.selectfont("Bitstream Vera Sans", 0, 0)
        dc.setfontsize(12)
        for lineno in xrange(len(self.buf)):
            line = self.buf[lineno]
            if self.bgcolors != None and lineno < len(self.bgcolors):
                for beg, end, rgba in self.bgcolors[lineno]:
                    cx0 = dc.textextents(line[:beg])[4]
                    cx1 = dc.textextents(line[:end])[4]
                    dc.setrgba(*rgba)
                    dc.rectangle(x0 + cx0, y - 11, cx1 - cx0, 14)
                    dc.fill()
            dc.setrgba(0, 0, 0, 1)
            dc.moveto(x0, y)
            dc.showtext(line)
            if lineno == self.cursor[1]:
                x = dc.textextents(line[:self.cursor[0]])[4]
                if self.view.hasfocus():
                    dc.setrgba(1, 0, 0, 1)
                else:
                    dc.setrgba(0.5, 0.5, 0.5, 1)
                dc.setlinewidth(1)
                dc.moveto(x0 + x + 0.5, y - 11)
                dc.lineto(x0 + x + 0.5, y + 3)
                dc.stroke()
            y += self.linespace

class thmctx:
    def __init__(self, vg):
        self.thmname = None
        self.sexpstack = []
        self.hypmap = {}
        self.state = 0
        self.proofctx = verify.ProofCtx()
        self.vg = vg
    def tok(self, tok):
        thestep = None
        if self.state == 0:
            if tok == 'thm':
                self.state = 1
            else:
                return 'expected thm'
        elif self.state == 1:
            if tok == '(':
                self.state = 2
            else:
                return 'expected ('
        elif self.state == 2:
            if tok in '()':
                return 'expected thm name'
            else:
                self.thmname = tok
                self.state = 3
        elif self.state == 3:
            if tok == '(':
                self.sexpstack.append([])
                self.state = 5
            else:
                return 'expected ( to open dv''s'
        elif self.state == 4:
            if tok == '(':
                self.sexpstack.append([])
                self.state = 7
            else:
                return 'expected ( to open hyps'
        elif self.state == 6:
            if tok == '(':
                self.sexpstack.append([])
                self.state = 9
            elif tok == ')':
                return 'expected proof stmt'
            else:
                thestep = tok
                self.state = 8
        elif self.state == 8:
            if tok == '(':
                self.state = 10
            else:
                return 'expected ( to open proof'
        elif self.state == 10:
            if tok == '(':
                self.sexpstack.append([])
                self.state = 11
            elif tok == ')':
                self.state = 12
            else:
                thestep = tok
        elif self.state in (5, 7, 9, 11):
            if tok == '(':
                self.sexpstack.append([])
            elif tok == ')':
                if len(self.sexpstack) == 1:
                    thestep = self.sexpstack[0]
                    self.sexpstack = []
                    self.state -= 1
                else:
                    last = self.sexpstack[-1]
                    del(self.sexpstack[-1])
                    self.sexpstack[-1].append(last)
            else:
                self.sexpstack[-1].append(tok)
        elif self.state == 12:
            if tok == ')':
                self.state = 13
            else:
                return 'expected )'
        elif self.state == 13:
            return 'extra junk after proof'
        if self.state == 6:
            for hyp in thestep:
                self.hypmap[hyp[0]] = hyp[1]
        elif self.state == 8:
            self.stmt = thestep
        elif thestep != None and self.state == 10:
            try:
                self.vg.check_proof_step(self.hypmap, thestep, self.proofctx)
            except verify.VerifyError, x:
                return str(x)
            except Exception, x:
                return `x`

class proof_view(editview):
    def updated(self):
        tc = thmctx(self.vg)
        status = None
        bgcolors = []
        for line in self.buf:
            bgcolorline = []
            for tok, beg, end in splitrange(line):
                status = tc.tok(tok)
                if status != None:
                    bgcolorline.append((beg, end, (1, .5, .5, 1)))
                    break
            bgcolors.append(bgcolorline)
            if status != None:
                break
        proofctx = tc.proofctx
        self.bgcolors = bgcolors
        self.stackview.clear()
        for wff in proofctx.stack:
            self.stackview.add_wff(wff)
        for term in proofctx.mandstack:
            self.stackview.add_term(term)
        if status != None:
            self.stackview.add_status(status)
        self.stackview.dirty()
        self.thmname = tc.thmname

class ascii_stack_view(editview):
    def clear(self):
        self.buf = []
        self.bgcolors = []
    def add_wff(self, wff):
        self.buf.append(verify.sexp_to_string(wff))
        self.bgcolors.append(())
    def add_term(self, term):
        termstr = verify.sexp_to_string(term[1])
        self.buf.append(termstr)
        self.bgcolors.append([(0, len(termstr), (1, .9, .6, 1))])
    def add_status(self, status):
        self.buf.append(status)
        self.bgcolors.append([(0, len(status), (1, .5, .5, 1))])
    def dirty(self):
        self.view.dirty()

def main(fn, loadfn, script):
    global pv
    global savefnbase
    global win

    if len(fn) >= 3 and fn[-3:] == '.gh':
        savefnbase = fn[:-3]
    else:
        savefnbase = 'untitled'

    win = x3.window(0, "ghilbert", my_callback)

    m = x3.menu(win, "File")
    x3.menuitem(m, "Save", "save", "<cmd>s")
    x3.menuitem(m, "Quit", "quit", "<cmd>q")

    m = x3.menu(win, "Help")
    x3.menuitem(m, "About...", "abou")

    panes = x3.vpane(win)

    pv = proof_view()
    x3.view(panes, 0x10104, pv)
    if script:
        page = display.x3page()
        typeset.read_script(page, file(script))
        pv.stackview = display.display_view(page)
        pv.vg = typeset.typeset_load_gh(page, fn, False)
    else:
        pv.stackview = ascii_stack_view()
        pv.vg = load_gh(fn)
    x3.view(panes, 0x10100, pv.stackview)
    win.setdefaultsize(600, 400)
    panes.setsizing(True, True, True, True)

    if loadfn != None:
        pv.buf = [line.strip('\r\n') for line in file(loadfn).xreadlines()]
        pv.updated()

    x3.main()

if __name__ == '__main__':
    import sys
    script = None
    argv = []
    i = 1
    while i < len(sys.argv):
        arg = sys.argv[i]
        if arg == '-script':
            script = sys.argv[i + 1]
            i += 1
        else:
            argv.append(arg)
        i += 1

    fn = argv[0]
    loadfn = None
    if len(argv) > 1:
        loadfn = argv[1]
    main(fn, loadfn, script)

