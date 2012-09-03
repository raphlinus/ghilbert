# license

import urllib

import verify
import cgi
import ghapp  # TODO: circular dep is not clean

from google.appengine.ext import webapp

def write_proof_line(out, line):
    line = line.rstrip()
    out.write('<div class="code">' + cgi.escape(line) + '</div>')

def write_intermediate_line(out, line, indent):
    line = line.rstrip()
    indent_em = 1.0 * indent
    out.write('<div style="margin-left: %gem"><span class="intermediate">' % indent_em + cgi.escape(line) + '</span></div>')

class ShowThmScanner:
    def __init__(self, instream):
        self.instream = instream
        self.lineno = 0
        self.toks = []
        self.tokix = 0
        self.notify_line = None
        self.linestash = []
    def get_tok(self):
        while len(self.toks) == self.tokix:
            line = self.instream.readline()
            self.linestash.append(line)
            if self.notify_line: self.notify_line.notify_line(line)
            self.lineno += 1
            if line == '':
                return None
            line = line.split('#')[0]
            line = line.replace('(', ' ( ')
            line = line.replace(')', ' ) ')
            self.toks = line.split()
            self.tokix = 0
        result = self.toks[self.tokix]
        self.tokix += 1
        return result
    def clear_linestash(self):
        self.linestash = []
    def start_recording(self, notify_line):
        self.notify_line = notify_line

class ShowThm:
    def __init__(self, s, out):
        self.s = s
        self.out = out
        self.proofctx = None
        self.tos_fresh = False

    # assume thm name has already been consumed
    def run(self, verifyctx):
        state = 3  # to match the state numbers in direct.js
        sexpstack = []
        concl = None
        while True:
            tok = self.s.get_tok()
            if tok is None:
                return 'unexpected eof'
            thestep = None
            #self.out.write('tok: ' + tok + ' ' + str(state) + '\n')
            if state == 3:
                if tok == '(':
                    sexpstack.append([])
                    state = 5
                else:
                    return 'expected dv list'
            elif state == 4:
                if tok == '(':
                    sexpstack.append([])
                    state = 7
                else:
                    return 'expected hyp list'
            elif state == 6:
                if tok == '(':
                    sexpstack.append([])
                    state = 9
                elif tok == ')':
                    return 'expected proof stmt'
                else:
                    thestep = tok
                    state = 8
            elif state == 8:
                if tok == '(':
                    sexpstack.append([])
                    state = 9
                elif tok == ')':
                    state = 10
                else:
                    thestep = tok
            elif state in (5, 7, 9):
                if tok == '(':
                    sexpstack.append([])
                elif tok == ')':
                    if len(sexpstack) == 1:
                        thestep = sexpstack.pop()
                        state -= 1
                    else:
                        last = sexpstack.pop()
                        sexpstack[-1].append(last)
                else:
                    sexpstack[-1].append(tok)
            if state == 4:
                self.out.write('dv list: ' + verify.sexp_to_string(thestep) + '\n')
                label = None  # doesn't seem to be needed
                fvmap = {}   # won't check these
                varmap = {}
                varlist = []
                proofctx = verify.ProofCtx(label, fvmap)
                proofctx.varmap = varmap
                proofctx.varlist = varlist
                self.proofctx = proofctx
            elif state == 6:
                self.out.write('hyps: ' + verify.sexp_to_string(thestep) + '\n')
                hypmap = {}
                for i in range(0, len(thestep), 2):
                    hypmap[thestep[i]] = thestep[i + 1]
                    pass
            elif state == 8 and concl is None:
                self.out.write('concl: ' + verify.sexp_to_string(thestep) + '\n')
                concl = thestep
            elif state == 8:
                #self.out.write('step: ' + verify.sexp_to_string(thestep) + '\n')
                verifyctx.check_proof_step(hypmap, thestep, proofctx)
                if len(proofctx.mandstack) == 0:
                    self.tos_fresh = True
                #self.out.write('proofctx stack len = %d\n' % len(proofctx.stack))
            elif state == 10:
                self.out.write('end of proof\n')
                break

    def notify_line(self, line):
        if self.tos_fresh:
            tos_str = verify.sexp_to_string(self.proofctx.stack[-1])
            write_intermediate_line(self.out, tos_str, len(self.proofctx.stack))
            self.tos_fresh = False
        write_proof_line(self.out, line)

class ShowThmRunner:
    def __init__(self, thmname, thmout):
        self.thmname = thmname
        self.thmout = thmout
    def run(self, urlctx, url, ctx, out):
        s = ShowThmScanner(urlctx.resolve(url))
        try:
            while 1:
                cmd = verify.read_sexp(s)
                if cmd is None:
                    # if we get here, we didn't find the thm
                    return True
                if type(cmd) != str:
                    raise SyntaxError('cmd must be atom: %s has type %s' % (cmd, type(cmd)))
                if cmd == 'thm':
                    tok = s.get_tok()
                    if tok != '(':
                        raise SyntaxError('expected thm start')
                    tok = s.get_tok()
                    if tok == self.thmname:
                        for line in s.linestash:
                            write_proof_line(self.thmout, line)
                        show_thm = ShowThm(s, self.thmout)
                        s.start_recording(show_thm)
                        show_thm.run(ctx)
                        return True
                    else:
                        arg = [tok]
                        while True:
                            sexp = verify.read_sexp(s)
                            if sexp == ')':
                                break
                            arg.append(sexp)
                else:
                    arg = verify.read_sexp(s)
                ctx.do_cmd(cmd, arg, out)
                s.clear_linestash()
        except verify.VerifyError, x:
            out.write('Verify error at %s:%d:\n%s' % (url, s.lineno, x.why))
        except SyntaxError, x:
            out.write('Syntax error at line %s:%d:\n%s' % (url, s.lineno, str(x)))
        ctx.countError()
        return False

class DevNull():
    def write(self, s):
        pass

class ShowThmPage(webapp.RequestHandler):
    def get(self, thmname):
        runner = ShowThmRunner(thmname, self.response.out)
        self.response.headers.add_header('content-type', 'text/html')
        o = self.response.out
        o.write('<html><head><title>Proof of %s</title>\n' % cgi.escape(thmname))
        o.write('<link rel=stylesheet href="/static/showthm.css" type="text/css">\n')
        o.write('</head>\n')
        o.write('<body><h1>Proof of %s</h1>\n' % cgi.escape(thmname))
        pipe = ghapp.get_all_proofs()
        url = '-'
        urlctx = verify.UrlCtx('', 'peano/peano_thms.gh', pipe)
        # We use the standard runner for imports and exports, but our own
        # special one for the topmost context.
        ctx = verify.VerifyCtx(urlctx, verify.run, False)
        runner.run(urlctx, url, ctx, DevNull())
        o.write('''<script src="/js/verify.js" type="text/javascript"></script>
<script src="/js/showthm.js" type="text/javascript"></script>
<script src="/js/typeset.js" type="text/javascript"></script>
<script type="text/javascript">
GH.typeset_intermediates()
</script>
''')
