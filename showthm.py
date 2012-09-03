# license

import verify
import ghapp  # TODO: circular dep is not clean

from google.appengine.ext import webapp

class ShowThmScanner:
    def __init__(self, instream, out):
        self.instream = instream
        self.lineno = 0
        self.toks = []
        self.tokix = 0
        self.out = out
        self.recording = False
        self.linestash = []
    def get_tok(self):
        while len(self.toks) == self.tokix:
            line = self.instream.readline()
            self.linestash.append(line)
            if self.recording: self.out.write(line)
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
    def start_recording(self):
        self.recording = True

class ShowThmRunner:
    def __init__(self, thmname, thmout):
        self.thmname = thmname
        self.thmout = thmout
    def run(self, urlctx, url, ctx, out):
        s = ShowThmScanner(urlctx.resolve(url), out)
        try:
            while 1:
                cmd = verify.read_sexp(s)
                if cmd is None:
                    return True
                if type(cmd) != str:
                    raise SyntaxError('cmd must be atom: %s has type %s' % (cmd, type(cmd)))
                arg = verify.read_sexp(s)
                if cmd == 'thm' and len(arg) and arg[0] == self.thmname:
                    self.thmout.write('whoo, processing ' + arg[0] + '\n')
                    self.thmout.write(''.join(s.linestash))
                    s.start_recording()
                    ctx.do_cmd(cmd, arg, out)
                    return True
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
        self.response.headers.add_header('content-type', 'text/plain')
        self.response.out.write('Hello there ' + thmname + '!\n')
        pipe = ghapp.get_all_proofs()
        url = '-'
        urlctx = verify.UrlCtx('', 'peano/peano_thms.gh', pipe)
        ctx = verify.VerifyCtx(urlctx, runner.run, False)
        ctx.run(urlctx, url, ctx, DevNull())


