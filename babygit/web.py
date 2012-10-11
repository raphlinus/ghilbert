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

import appengine
import zlib
import logging
import cgi
import urllib
import hashlib
import zlib
import struct

import babygit
import repo
import stage

from google.appengine.ext import webapp

#s = babygit.FsStore()

s = appengine.AEStore()

def init_test_repo():
    babygit.put_test_repo(s)

    r = repo.Repo(s)
    stage.checkout(r) 
    tree = stage.getroot(r)
    tree = stage.save(r, 'dir/newfile', 'This is a new file!\n', tree)
    tree = stage.save(r, 'dir/anotherfile', 'This is another new file!\n', tree)
    tree = stage.save(r, 'dir/newfile', 'Replace contents\n', tree)
    stage.add(r, tree)
    stage.commit(r, 'Author <author@ghilbert.org>', 'Test adding a new file\n')

def packetstr(payload):
    return '%04x' % (len(payload) + 4) + payload

class handler(webapp.RequestHandler):
    def __init__(self):
        self.store = s
        self.repo = repo.Repo(s)

    def smart_upload_pack(self):
        response = [packetstr('# service=git-upload-pack\n')]
        response.append('0000')
        caps = 'thin-pack ofs-delta no-progress'
        inforefs = s.getinforefs()
        head_sha = inforefs['refs/heads/master']
        response.append(packetstr(head_sha + ' HEAD\x00' + caps + '\n'))
        for ref, sha in inforefs.iteritems():
            response.append(packetstr(sha + ' ' + ref + '\n'))
        response.append('0000')
        self.response.headers['Content-Type'] = 'application/x-git-upload-pack-advertisement'
        self.response.out.write(''.join(response))

    def get(self, arg):
        if arg == 'HEAD':
            self.response.out.write('ref: refs/heads/master\n')
        elif arg == 'info/refs':
            service = self.request.get('service')
            if service == 'git-upload-pack':
                return self.smart_upload_pack()
            inforefs = s.getinforefs()
            infostr = ''.join(['%s\t%s\n' % (sha, ref) for
                ref, sha in inforefs.iteritems()])
            self.response.out.write(infostr)
        elif arg.startswith('objects/') and arg[10] == '/':
            sha = arg[8:10] + arg[11:49]
            compressed = s.getobjz(sha)
            self.response.headers['Content-Type'] = 'application/octet-stream'
            self.response.out.write(compressed)
        elif arg.startswith('edit/'):
            editurl = arg[5:]
            obj = self.repo.traverse(editurl)
            if obj is None:
                self.response.out.write('404 not found')
            elif babygit.obj_type(obj) == 'blob':
                contents = babygit.obj_contents(obj)
                self.response.out.write('<html><title>Editing: ' + cgi.escape(editurl) + '</title>\n')
                self.response.out.write('<body>\n')
                self.response.out.write('<h1>Editing ' + cgi.escape(editurl) + '</h1>\n')
                self.response.out.write('<form method="post" action="/git/save/' + urllib.quote(editurl) + '">\n')
                self.response.out.write('<textarea cols="80" rows="24" name="content">\n')
                for line in contents.split('\n'):
                    self.response.out.write(cgi.escape(line) + '\n')
                self.response.out.write('</textarea>')
                self.response.out.write('<br />\n')
                self.response.out.write('<input type="submit" value="Save">\n')

        else:
            # try to serve a raw blob
            obj = self.repo.traverse(arg)
            if obj is None:
                self.response.out.write('404 not found')
            elif babygit.obj_type(obj) == 'blob':
                self.response.headers['Content-Type'] = 'text/plain';
                contents = babygit.obj_contents(obj)
                self.response.out.write(contents)
            else:
                ptree = self.repo.parse_tree(obj)
                html = ['<html><ul>']
                for mode, name, sha in ptree:
                    fn = name
                    if mode == '40000': fn += '/'
                    html.append('<li><a href="' + fn + '">' + fn + '</a></li>\n')
                self.response.out.write(''.join(html))

    def parse_pktlines(self, data):
        i = 0
        result = []
        while i < len(data):
            size = int(data[i:i+4], 16)
            if size == 0:
                result.append(None)
                i += 4
            else:
                result.append(data[i+4:i+size])
                i += size
        return result

    obj_types = {'commit': 1, 'tree': 2, 'blob': 3, 'tag': 4}
    def encode_type_and_size(self, t, size):
        t_num = self.obj_types[t]
        if size > 16: hibit = 0x80
        else: hibit = 0
        result = [chr(hibit | (t_num << 4) | (size & 15))]
        size >>= 4
        while size:
            if size > 128: hibit = 0x80
            else: hibit = 0
            result.append(chr(hibit | (size & 127)))
            size >>= 7
        return ''.join(result)

    def send_packfile(self, objs, out):
        m = hashlib.sha1()
        header = 'PACK' + struct.pack('>II', 2, len(objs))
        out.write(header)
        m.update(header)
        for ref, obj in objs:
            t = babygit.obj_type(obj)
            s = babygit.obj_size(obj)
            #if s != len(babygit.obj_contents(obj)):
            #    logging.debug('size mismatch')
            enc_t_s = self.encode_type_and_size(t, s)
            out.write(enc_t_s)
            m.update(enc_t_s)
            compressed = zlib.compress(babygit.obj_contents(obj))
            out.write(compressed)
            m.update(compressed)
        out.write(m.digest())

    def post(self, arg):
        if arg == 'git-upload-pack':
            lines = self.parse_pktlines(self.request.body)
            wants = set()
            haves = set()
            for l in lines:
                if l is None:
                    break
                if l.startswith('want '):
                    wants.add(l.rstrip('\n').split(' ')[1])
            objs = self.repo.walk(wants, haves)
            self.response.headers['Content-Type'] = 'application/x-git-upload-pack-result'
            o = self.response.out
            o.write(packetstr('NAK\n'))
            self.send_packfile(objs, o)
        if arg.startswith('save/'):
            editurl = arg[5:]
            stage.checkout(self.repo)
            tree = stage.getroot(self.repo)
            tree = stage.save(self.repo, editurl, self.request.get('content'))
            stage.add(self.repo, tree)
            author = 'Author <author@ghilbert.org>'
            msg = 'Commit from wiki\n'
            commitsha = stage.commit(self.repo, author, msg)
            self.response.out.write('saved ' + cgi.escape(editurl) + ' with commit ' + commitsha + '\n')

