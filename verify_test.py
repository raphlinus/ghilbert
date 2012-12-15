#encoding: utf-8
import sys
import verify

class StringStream:
     def __init__(self, s):
          self.lines = s.split('\n')
          self.ix = 0
     def readline(self):
          if self.ix >= len(self.lines):
               return ''
          else:
               result = self.lines[self.ix] + '\n'
               self.ix += 1
               return result

class TestUrlCtx:
     def __init__(self):
          self.d = {}
     def add(self, url, val):
          self.d[url] = val
     def resolve(self, url):
          return StringStream(self.d[url])

     # additional interface for data-driven tests
     def open_append(self, url):
          self.current_url = url
          if not self.d.has_key(url):
               self.d[url] = ''
          self.saved_value = self.d[url]
     def append_current(self, text):
          self.d[self.current_url] += text
     def revert(self):
          self.d[self.current_url] = self.saved_value

def sexp(s):
     stream = StringStream(s)
     return verify.read_sexp(verify.Scanner(stream))

def test_one_fv(verifyctx, expected, var, term, fvctx = None):
     free = verifyctx.free_in(var, sexp(term), fvctx)
     if free: explanation = "free in"
     else: explanation = "not free in"
     if verbose or free != expected: print var, explanation, term
     if free != expected:
          raise verify.VerifyError('fail')

def TestFv(out):
     urlctx = TestUrlCtx()
     urlctx.add('foo.ghi',
"""kind (wff)
kind (nat)
tvar (wff ph ps)
tvar (nat A B)
var (nat x y)
term (wff (= A B))
term (wff (A. x ph))
term (wff ([/] A x ph) (x A))
""")
     verifyctx = verify.VerifyCtx(urlctx, run_regression)
     verifyctx.do_cmd('import', ['FOO', 'foo.ghi', [], '""'], out)
     verifyctx.do_cmd('tvar', ['nat', 'A', 'B'], out)
     verifyctx.do_cmd('var', ['nat', 'x', 'y'], out)
     test_one_fv(verifyctx, True, 'x', '(= x y)')
     test_one_fv(verifyctx, False, 'z', '(= x y)')
     test_one_fv(verifyctx, False, 'x', '(A. x ph)')
     test_one_fv(verifyctx, True, 'x', '([/] (= x y) x ph)')
     test_one_fv(verifyctx, False, 'x', '([/] A x ph)')
     test_one_fv(verifyctx, True, 'x', 'x')
     test_one_fv(verifyctx, False, 'x', 'y')
     fvvars_x = {'A': 0}
     fvvars_y = {}
     test_one_fv(verifyctx, False, 'x', 'A', fvvars_x)
     test_one_fv(verifyctx, True, 'y', 'A', fvvars_y)
     test_one_fv(verifyctx, False, 'z', 'A')
     test_one_fv(verifyctx, True, 'x', 'x', fvvars_x)
     test_one_fv(verifyctx, False, 'x', 'y', fvvars_x)

def TestStmt(out):
     urlctx = TestUrlCtx()
     urlctx.add('foo.ghi',
"""kind (wff)
kind (nat)
tvar (wff ph ps)
tvar (nat A B)
var (nat x y)
term (wff (= A B))
term (wff (-> ph ps))
term (wff (A. x ph))
stmt (19.21ai ((ph x)) ((-> ph ps)) (-> ph (A. x ps)))
""")     
     verifyctx = verify.VerifyCtx(urlctx, run_regression)
     verifyctx.do_cmd('import', ['FOO', 'foo.ghi', [], '"foo."'], out)
     print verifyctx.syms

def TestThm(out):
     urlctx = TestUrlCtx()
     urlctx.add('foo.ghi',
"""kind (wff)
kind (nat)
tvar (wff ph ps)
tvar (nat A B)
var (nat x y)
term (wff (= A B))
term (wff (-> ph ps))
term (wff (A. x ph))
stmt (19.21ai ((ph x)) ((-> ph ps)) (-> ph (A. x ps)))
""")     
     verifyctx = verify.VerifyCtx(urlctx, run_regression)
     verifyctx.do_cmd('import', ['FOO', 'foo.ghi', [], '""'], out)
     verifyctx.do_cmd('tvar', ['wff', 'ph', 'ps'], out)
     verifyctx.do_cmd('var', ['nat', 'x', 'y'], out)
     verifyctx.do_cmd('thm', ['19.21ai2', [['ph', 'x']],
                              ['hyp', ['->', 'ph', 'ps']],
                              ['->', 'ph', ['A.', 'x', 'ps']],
                              'hyp', 'x', '19.21ai'], out)
     print verifyctx.syms

# Version of run loop tuned for regression testing
def run_regression(urlctx, url, ctx, out):
    s = verify.Scanner(urlctx.resolve(url))
    while 1:
         cmd = verify.read_sexp(s)
         if cmd is None:
              return True
         if type(cmd) != str:
              raise SyntaxError('cmd must be atom')
         arg = verify.read_sexp(s)
         ctx.do_cmd(cmd, arg, out)

def regression(fn, out):
     tests = 0
     failures = 0

     urlctx = TestUrlCtx()
     lineno = 0
     for l in file(fn).xreadlines():
          lineno += 1
          if l.startswith('!'):
               cmd = l.split()
               if cmd[0] == '!append':
                    urlctx.open_append(cmd[1])
                    dosave = False
               elif cmd[0] == '!save':
                    dosave = True
               elif cmd[0] in ('!accept', '!reject'):
                    verifyctx = verify.VerifyCtx(urlctx, run_regression)
                    error = None
                    tests += 1
                    try:
                         run_regression(urlctx, cmd[1], verifyctx, out)
                    except verify.VerifyError, x:
                         error = "VerifyError: " + x.why
                    except SyntaxError, x:
                         error = "SyntaxError: " + str(x)
                    if error is None and cmd[0] == '!reject':
                         failures += 1
                         print str(lineno) + ': FAIL, expected error: ' + ' '.join(cmd[2:])
                    elif error and cmd[0] == '!accept':
                         failures += 1
                         print str(lineno) + ': FAIL, got unexpected ' + error
                    if verbose >= 1 and error and cmd[0] == '!reject':
                         print str(lineno) + ': ok ' + error
                    if not dosave:
                         urlctx.revert()
          elif l.strip() and not l.startswith('#'):
               urlctx.append_current(l)
     return [tests, failures]

verbose = 1
TestFv(sys.stdout)
TestStmt(sys.stdout)
TestThm(sys.stdout)
if len(sys.argv) > 1:
     tests, failures = regression(sys.argv[1], sys.stdout)
     print
     print tests, 'tests run, ', failures, 'failures'
     exit(0 if failures == 0 else 1)
