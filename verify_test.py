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
     def normalize(self, url, fname):
          return url
     def resolve(self, url, fname):
          f = StringStream(self.d[url])
          return verify.ScannerRec(f)

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

class TestGlobalCtx(verify.GlobalCtx):
     def __init__(self, urlctx):
          verify.GlobalCtx.__init__(self, urlctx)
     def run(self, scanner, url, ctx):
          return run_regression(scanner, url, ctx)

def sexp(s):
     stream = StringStream(s)
     return verify.read_sexp(verify.ScannerRec(stream))

def test_one_fv(verifyctx, expected, var, term, fvctx = None):
     varlist = []
     varmap = {}
     try:
          e = verifyctx.internalize(sexp(term), varlist, varmap)
          if var not in varmap:
               verifyctx.internalize(var, varlist, varmap)
          if fvctx != None:
               fvc_int = {}
               for v in fvctx.iterkeys():
                    u = verifyctx.internalize(v, varlist, varmap)
                    fvc_int[u[2]] = 0
               fvctx = fvc_int
                    
     except verify.VerifyError, x:
          print 'Verify Error: %s' % x.why
          raise
     free = verifyctx.free_in(varmap[var], e[2], fvctx, varlist)
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
term (nat (+ A B))
""")
     gctx = TestGlobalCtx(urlctx)
     verifyctx = verify.VerifyCtx(gctx, "")
     verifyctx.out = out
     verifyctx.do_cmd('import', ['FOO', 'foo.ghi', [], '""'])
     verifyctx.do_cmd('tvar', ['nat', 'A', 'B'])
     verifyctx.do_cmd('var', ['nat', 'x', 'y', 'z'])
     verifyctx.do_cmd('tvar', ['wff', 'ph'])
     test_one_fv(verifyctx, True, 'x', '(= x y)')
     test_one_fv(verifyctx, False, 'z', '(= x y)')
     test_one_fv(verifyctx, False, 'x', '(A. x ph)')
     test_one_fv(verifyctx, True, 'x', '([/] (+ x y) x ph)')
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
     gctx = TestGlobalCtx(urlctx)
     verifyctx = verify.VerifyCtx(gctx, "")
     verifyctx.out = out
     verifyctx.do_cmd('import', ['FOO', 'foo.ghi', [], '"foo."'])
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
     gctx = TestGlobalCtx(urlctx)
     verifyctx = verify.VerifyCtx(gctx, "")
     verifyctx.do_cmd('import', ['FOO', 'foo.ghi', [], '""'])
     verifyctx.do_cmd('tvar', ['wff', 'ph', 'ps'])
     verifyctx.do_cmd('var', ['nat', 'x', 'y'])
     verifyctx.do_cmd('thm', ['19.21ai2', [['ph', 'x']],
                              ['hyp', ['->', 'ph', 'ps']],
                              ['->', 'ph', ['A.', 'x', 'ps']],
                              'hyp', 'x', '19.21ai'])
     print verifyctx.syms

# Version of run loop tuned for regression testing
def run_regression(scanner, url, ctx):
     while 1:
         cmd = verify.read_sexp(scanner)
         if cmd is None:
              return True
         if type(cmd) != str:
              raise SyntaxError('cmd must be atom')
         arg = verify.read_sexp(scanner)
         #print '%s %s' % (cmd, verify.sexp_to_string(arg))
         ctx.do_cmd(cmd, arg)

def regression(fn, out):
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
                    gctx = TestGlobalCtx(urlctx)
                    verifyctx = verify.VerifyCtx(gctx, cmd[1])
                    verifyctx.out = out
                    error = None
                    try:
                         scanner = urlctx.resolve(cmd[1], '.')
                         gctx.run(scanner, cmd[1], verifyctx)
                    except verify.VerifyError, x:
                         error = "VerifyError: " + x.why
                    except SyntaxError, x:
                         error = "SyntaxError: " + str(x)
                    if error is None and cmd[0] == '!reject':
                         print str(lineno) + ': FAIL, expected error: ' + ' '.join(cmd[2:])
                    elif error and cmd[0] == '!accept':
                         print str(lineno) + ': FAIL, got unexpected ' + error
                    if verbose >= 1 and error and cmd[0] == '!reject':
                         print str(lineno) + ': ok ' + error
                    if not dosave:
                         urlctx.revert()
          elif l.strip() and not l.startswith('#'):
               urlctx.append_current(l)

verbose = 1
TestFv(sys.stdout)
TestStmt(sys.stdout)
TestThm(sys.stdout)
if len(sys.argv) > 1:
     regression(sys.argv[1], sys.stdout)
