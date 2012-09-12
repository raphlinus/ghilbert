from google.appengine.ext import webapp
import babygit
import zlib

s = babygit.m

class handler(webapp.RequestHandler):
    def get(self, arg):
        if arg == 'HEAD':
            self.response.out.write('ref: refs/heads/master\n')
        elif arg == 'info/refs':
            self.response.out.write(s.getinforefs())
        elif arg.startswith('objects/') and arg[10] == '/':
            sha = arg[8:10] + arg[11:49]
            obj = s.getobj(sha)
            compressed = zlib.compress(obj)
            self.response.headers['Content-Type'] = 'application/octet-stream'
            self.response.out.write(compressed)


