import babygit
import appengine
import zlib
import logging

from google.appengine.ext import webapp

s = appengine.AEStore()
babygit.put_test_repo(s)

class handler(webapp.RequestHandler):
    def get(self, arg):
        if arg == 'HEAD':
            self.response.out.write('ref: refs/heads/master\n')
        elif arg == 'info/refs':
            inforefs = s.getinforefs()
            logging.debug(`inforefs`)
            infostr = ''.join(['%s\t%s\n' % (sha, ref) for
                ref, sha in inforefs.iteritems()])
            self.response.out.write(infostr)
        elif arg.startswith('objects/') and arg[10] == '/':
            sha = arg[8:10] + arg[11:49]
            obj = s.getobj(sha)
            compressed = zlib.compress(obj)
            self.response.headers['Content-Type'] = 'application/octet-stream'
            self.response.out.write(compressed)


