import appengine
import zlib
import logging

import babygit
import repo

from google.appengine.ext import webapp

#s = appengine.AEStore()
s = babygit.FsStore()
#babygit.put_test_repo(s)

class handler(webapp.RequestHandler):
    def __init__(self):
        self.store = s
        self.repo = repo.Repo(s)
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
            compressed = s.getobjz(sha)
            self.response.headers['Content-Type'] = 'application/octet-stream'
            self.response.out.write(compressed)
        else:
            # try to serve a raw blob
            splitpath = arg.split('/')
            if splitpath[-1] == '': splitpath.pop()
            sha = self.repo.getroot()
            obj = self.store.getobj(sha)
            ptree = self.repo.parse_tree(obj)
            for i in range(len(splitpath)):
                mode, sha = self.repo.find_in_tree(ptree, splitpath[i])
                obj = self.store.getobj(sha)
                t = babygit.obj_type(obj)
                if t == 'blob':  # could use mode before fetching obj
                    self.response.headers['Content-Type'] = 'text/plain';
                    self.response.out.write(obj[obj.find('\x00') + 1:])
                    return
                else:
                    ptree = self.repo.parse_tree(obj)
            html = ['<html><ul>']
            for mode, name, sha in ptree:
                fn = name
                if mode == '40000': fn += '/'
                html.append('<li><a href="' + fn + '">' + fn + '</a></li>\n')
            self.response.out.write(''.join(html))

