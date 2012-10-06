# Copyright 2012 Google Inc.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import logging
import urllib

import verify
import cgi
import ghapp  # TODO: circular dep is not clean

import django.utils.simplejson as json

from google.appengine.ext import webapp

class ProofFormatter:
    def __init__(self, out, style):
        self.out = out
        self.style = style
        self.out_buf = []
        self.space_indent = 8  # in px units; em is not consistent across fonts

    def header(self, thmname):
        o = self.out
        o.write('<html><head><title>Proof of %s</title>\n' % cgi.escape(thmname))
        o.write('<link rel=stylesheet href="/static/showthm.css" type="text/css">\n')
        o.write('</head>\n')
        o.write('<body><h1>Proof of %s</h1>\n' % cgi.escape(thmname))
    def write_proof_line(self, line):
        line = line.rstrip()
        sline = line.lstrip()
        indent_px = (len(line) - len(sline)) * self.space_indent
        self.out.write('<div style="margin-left: %gpx" class="code">' % indent_px + sline + '</div>\n')
    def write_proof_tokens(self, tokens):
        self.out_buf.append(cgi.escape(''.join(tokens)))
    def proof_newline(self):
        self.write_proof_line(''.join(self.out_buf))
        self.out_buf = []
    def write_proof_step(self, step, is_linkable):
        step_html = '<span class="step">' + cgi.escape(step) + '</span>'
        if is_linkable:
            url = '/showthm/' + urllib.quote(step)
            self.out_buf.append('<a href="%s">%s</a>' % (url, step_html))
        else:
            self.out_buf.append(step_html)
    def write_intermediate_line(self, line, indent):
        line = line.rstrip()
        indent_px = self.space_indent * 2 * indent
        self.out.write('<div style="margin-left: %gpx"><span class="intermediate">' % indent_px + cgi.escape(line) + '</span></div>\n')
    def done(self):
        line = ''.join(self.out_buf)
        if len(line):
            self.write_proof_line(line)
        self.out.write(
'''<script src="/js/verify.js" type="text/javascript"></script>
<script src="/js/showthm.js" type="text/javascript"></script>
<script src="/js/typeset.js" type="text/javascript"></script>
<script type="text/javascript">
GH.typeset_intermediates()
</script>
''')
    def write_trace(self, trace):
        o = self.out
        o.write('<script type="text/javascript">\n')
        o.write('var trace = ' + json.dumps(trace) + '\n')
        o.write('</script>\n')
        o.write('<script src="/js/showthmstep.js" type="text/javascript"></script>\n')
        o.write('<div id="stack">Stack</div>\n')


def display_404(response, thmname):
    response.set_status(404)
    response.out.write(
'''<html><head><title>Not found</title></head>
<body>
<h1>Not found</h1>
<p>The theorem %s was not found, sorry.</p>
''' % cgi.escape(thmname))
    
class ShowThmScanner:
    def __init__(self, instream):
        self.instream = instream
        self.lineno = 0
        self.line = ''
        self.ix = 0
        self.listener = None
        self.linestash = []
    def next_tok(self, ix):
        len_line = len(self.line)
        while ix < len_line:
            c = self.line[ix]
            if c.isspace():
                ix += 1
            elif c == '#':
                return len_line
            else:
                return ix
        return ix
    def get_tok(self):
        listener = self.listener
        start_ix = self.ix
        ix = self.next_tok(start_ix)
        while len(self.line) == ix:
            if listener:
                if ix > start_ix:
                    listener.notify_whitespace(self.line[start_ix:ix])
                listener.notify_newline()
            self.line = self.instream.readline()
            self.lineno += 1
            if self.line == '':
                return None
            self.linestash.append(self.line)
            start_ix = 0
            ix = self.next_tok(start_ix)
        if listener and ix > start_ix:
            listener.notify_whitespace(self.line[start_ix:ix])
        c = self.line[ix]
        end_ix = ix + 1
        if not c in '()':
            len_line = len(self.line)
            while end_ix < len_line:
                c = self.line[end_ix]
                if c.isspace() or c in '()#':
                    break
                end_ix += 1
        self.ix = end_ix
        tok = self.line[ix:end_ix]
        if listener: listener.notify_tok(tok)
        return tok

    def start_recording(self, listener):
        self.listener = listener

    def clear_linestash(self):
        self.linestash = []

    # Gets the linestash up to the current index, i.e. if you do this at
    # the same time as start_recording, then the two will be contiguous.
    def get_linestash(self):
        if len(self.linestash):
            self.linestash[-1] = self.linestash[-1][:self.ix]
        return self.linestash

# Remove saved drafts, they're not actually part of the description
def trim_description(lines):
    i = len(lines)
    while i > 0:
        if lines[i - 1].startswith('#!'): break
        i -= 1
    return lines[i:]

class ShowThm:
    def __init__(self, s, out, linkable_thms, style):
        self.s = s
        self.out = out
        self.linkable_thms = linkable_thms
        self.style = style
        self.proofctx = None
        self.tos_fresh = False
        self.accum = []  # tokens of raw proof to accumulate
        self.formatter = ProofFormatter(out, style)

    def header(self, thmname):
        self.formatter.header(thmname)
    def write_linestash(self, linestash):
        description = trim_description(linestash)
        for i in range(len(description) - 1):
            self.formatter.write_proof_line(description[i])
        self.formatter.out_buf.append(description[-1])

    # assume thm name has already been consumed
    def run(self, verifyctx):
        trace = []
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
                #self.out.write('dv list: ' + verify.sexp_to_string(thestep) + '\n')
                label = None  # doesn't seem to be needed
                fvmap = {}   # won't check these
                varmap = {}
                varlist = []
                proofctx = verify.ProofCtx(label, fvmap)
                proofctx.varmap = varmap
                proofctx.varlist = varlist
                self.proofctx = proofctx
            elif state == 6:
                #self.out.write('hyps: ' + verify.sexp_to_string(thestep) + '\n')
                hypmap = {}
                for i in range(0, len(thestep), 2):
                    hypmap[thestep[i]] = thestep[i + 1]
                    pass
            elif state == 8 and concl is None:
                #self.out.write('concl: ' + verify.sexp_to_string(thestep) + '\n')
                concl = thestep
            elif state == 8:
                #self.out.write('step: ' + verify.sexp_to_string(thestep) + '\n')
                stack_len_before = len(proofctx.stack)
                verifyctx.check_proof_step(hypmap, thestep, proofctx)
                if len(proofctx.mandstack) == 0:
                    if self.style == 'step':
                        n_popped = stack_len_before - len(proofctx.stack) + 1
                        step_string = verify.sexp_to_string(proofctx.stack[-1])
                        trace.append([n_popped, step_string])
                    self.accum.pop()
                    self.output_accum()
                    is_linkable = thestep in self.linkable_thms
                    self.formatter.write_proof_step(thestep, is_linkable)
                    self.tos_fresh = True
                #self.out.write('proofctx stack len = %d\n' % len(proofctx.stack))
            elif state == 10:
                self.notify_newline()
                self.formatter.done()
                if self.style == 'step':
                    self.formatter.write_trace(trace)
                break
    def notify_whitespace(self, whitespace):
        self.accum.append(whitespace)
    def notify_tok(self, tok):
        self.accum.append(tok)
    def notify_newline(self):
        self.output_accum()
        self.formatter.proof_newline()
        if self.tos_fresh:
            tos_str = verify.sexp_to_string(self.proofctx.stack[-1])
            if self.style == 'interleaved':
                self.formatter.write_intermediate_line(tos_str, len(self.proofctx.stack))
            self.tos_fresh = False
    def output_accum(self):
        self.formatter.write_proof_tokens(self.accum)
        self.accum = []

class ShowThmRunner:
    def __init__(self, thmname, response, style):
        self.thmname = thmname
        self.response = response
        self.linkable_thms = set()
        self.style = style
    def run(self, urlctx, url, ctx, out):
        s = ShowThmScanner(urlctx.resolve(url))
        try:
            while 1:
                cmd = verify.read_sexp(s)
                if cmd is None:
                    display_404(self.response, self.thmname)
                    return True
                if type(cmd) != str:
                    raise SyntaxError('cmd must be atom: %s has type %s' % (cmd, type(cmd)))
                if cmd == 'thm':
                    tok = s.get_tok()
                    if tok != '(':
                        raise SyntaxError('expected thm start')
                    tok = s.get_tok()
                    if tok == self.thmname:
                        show_thm = ShowThm(s, self.response.out, self.linkable_thms, self.style)
                        show_thm.header(self.thmname)
                        show_thm.write_linestash(s.get_linestash())
                        s.start_recording(show_thm)
                        show_thm.run(ctx)
                        return True
                    else:
                        self.linkable_thms.add(tok)
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
        style = self.request.get('style', 'interleaved') 
        runner = ShowThmRunner(thmname, self.response, style)
        self.response.headers.add_header('content-type', 'text/html')
        pipe = ghapp.get_all_proofs()
        url = '-'
        urlctx = verify.UrlCtx('', 'peano/peano_thms.gh', pipe)
        # We use the standard runner for imports and exports, but our own
        # special one for the topmost context.
        ctx = verify.VerifyCtx(urlctx, verify.run, False)
        runner.run(urlctx, url, ctx, DevNull())

# This is a separate page but is in this module because so much of the
# functionality is similar.
class ListThmsPage(webapp.RequestHandler):
    def get(self, arg):
        o = self.response.out
        o.write(
'''<html><head><title>List ot theorems</title></head>
<body>
<h1>List of theorems</h1>
<p>A list of all theorems (currently just the peano module):</p>
''')
        pipe = ghapp.get_all_proofs()
        runner = ListThmsRunner()
        url = '-'
        urlctx = verify.UrlCtx('', 'peano/peano_thms.gh', pipe)
        # We use the standard runner for imports and exports, but our own
        # special one for the topmost context.
        ctx = verify.VerifyCtx(urlctx, verify.run, False)
        runner.run(urlctx, url, ctx, DevNull())
        for thm, lines in runner.thmlist:
            lines = trim_description(lines)
            description = []
            for i in range(len(lines)):
                line = lines[i].strip()
                if line.startswith('#'):
                    description.append(line[1:].lstrip())
                elif len(line) != 0:
                    break
            descstr = ' '.join(description)
            if len(descstr) > 80:
                descstr = descstr[:78] + '...'
            url = '/showthm/' + urllib.quote(thm)
            o.write('<div><a href="%s">%s</a> %s</div>\n' % \
                (url, cgi.escape(thm), cgi.escape(descstr)))

class ListThmsRunner:
    def __init__(self):
        self.thmlist = []
    def run(self, urlctx, url, ctx, out):
        s = ShowThmScanner(urlctx.resolve(url))
        try:
            while 1:
                cmd = verify.read_sexp(s)
                if cmd is None:
                    return True
                if type(cmd) != str:
                    raise SyntaxError('cmd must be atom: %s has type %s' % (cmd, type(cmd)))
                arg = verify.read_sexp(s)
                if cmd == 'thm' and len(arg):
                    self.thmlist.append((arg[0], s.get_linestash()))
                ctx.do_cmd(cmd, arg, out)
                s.clear_linestash()
        except verify.VerifyError, x:
            out.write('Verify error at %s:%d:\n%s' % (url, s.lineno, x.why))
        except SyntaxError, x:
            out.write('Syntax error at line %s:%d:\n%s' % (url, s.lineno, str(x)))
        ctx.countError()
        return False

