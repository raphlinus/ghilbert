import appengine
import zlib
import logging

import babygit
import repo
import stage

from google.appengine.ext import webapp

#s = babygit.FsStore()

s = appengine.AEStore()
babygit.put_test_repo(s)

r = repo.Repo(s)
stage.checkout(r) 
tree = stage.getroot(r)
tree = stage.save(r, 'dir/newfile', 'This is a new file!\n', tree)
tree = stage.save(r, 'dir/anotherfile', 'This is another new file!\n', tree)
tree = stage.save(r, 'dir/newfile', 'Replace contents\n', tree)
stage.add(r, tree)
stage.commit(r, 'Author <author@ghilbert.org>', 'Test adding a new file\n')

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
            obj = self.repo.traverse(arg)
            if obj is None:
                self.response.out.write('404 not found')
            elif babygit.obj_type(obj) == 'blob':
                self.response.headers['Content-Type'] = 'text/plain';
                self.response.out.write(obj[obj.find('\x00') + 1:])
            else:
                ptree = self.repo.parse_tree(obj)
                html = ['<html><ul>']
                for mode, name, sha in ptree:
                    fn = name
                    if mode == '40000': fn += '/'
                    html.append('<li><a href="' + fn + '">' + fn + '</a></li>\n')
                self.response.out.write(''.join(html))

