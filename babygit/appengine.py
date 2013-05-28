import hashlib
import logging
import zlib
import time
import datetime

from google.appengine.api import files
from google.appengine.api import memcache
from google.appengine.ext import blobstore
from google.appengine.ext import db
from google.appengine.ext.webapp import blobstore_handlers

from webapp2_extras import json

import store

class Obj(db.Model):
    # key is the sha hash
    blob = blobstore.BlobReferenceProperty(indexed=False)

class Pack(db.Model):
    idx = blobstore.BlobReferenceProperty(indexed=False)
    blob = blobstore.BlobReferenceProperty(indexed=False)
    date = db.DateTimeProperty(auto_now=True)

class Ref(db.Model):
    # key is the refname (eg 'refs/heads/master')
    sha = db.StringProperty()

class Stage(db.Model):
    # the key should probably be the userid
    parentcommit = db.StringProperty()
    tree = db.StringProperty()
    date = db.DateTimeProperty(auto_now=True)

class Blobcache:
    blocksize = 524288
    nblocks = 8
    def __init__(self):
        self.blocks = {}
        self.atime = 0
    def readblock(self, blobinfo, key, blocknum):
        thekey = key + "_" + str(blocknum)
        if not self.blocks.has_key(thekey):
            if len(self.blocks) >= Blobcache.nblocks:
                # evict
                minatime = None
                minkey = None
                for k in self.blocks:
                    if minatime is None or self.blocks[k][1] < minatime:
                        minatime = self.blocks[k][1]
                        minkey = k
                del self.blocks[minkey]
            reader = blobstore.BlobReader(blobinfo)
            reader.seek(Blobcache.blocksize * blocknum)
            data = reader.read(Blobcache.blocksize)
            reader.close()
            self.blocks[thekey] = [data, self.atime]
        self.blocks[thekey][1] = self.atime
        self.atime += 1
        return self.blocks[thekey][0]

    class Reader:
        def __init__(self, bc, blobinfo, off):
            self.bc = bc
            self.blobinfo = blobinfo
            self.key = str(blobinfo.key())
            self.seek(off)
        def seek(self, off):
            self.blocknum = off / Blobcache.blocksize
            self.blockoff = off % Blobcache.blocksize
        def read(self, size):
            result = []
            remaining = size
            while remaining:
                block = self.bc.readblock(self.blobinfo, self.key, self.blocknum)
                blockend = min(Blobcache.blocksize, self.blockoff + remaining)
                result.append(block[self.blockoff:blockend])
                n = blockend - self.blockoff
                remaining -= n
                self.blockoff += n
                if self.blockoff == Blobcache.blocksize:
                    self.blockoff = 0
                    self.blocknum += 1
            return ''.join(result)

    def open(self, blobinfo, off):
        return Blobcache.Reader(self, blobinfo, off)

# Using a global is a bit ugly, but oh well. It's also not great that
# each copy creates its own "packs", but the lossage is minimal.
gBlobcache = None

class AEStore(store.Store):
    def __init__(self):
        global gBlobcache
        if gBlobcache is None:
            gBlobcache = Blobcache()
        self.packs = None
        self.blobcache = gBlobcache

    def getlooseobj(self, sha):
        obj = memcache.get(sha, namespace='obj')
        if obj is not None:
            return obj
        obj = Obj.get_by_key_name(sha)
        if not obj:
            return None
        buffer_size = min(1048576, obj.blob.size)
        blob_reader = blobstore.BlobReader(obj.blob, buffer_size = buffer_size)
        result = blob_reader.read()
        blob_reader.close()
        if result and len(result) < 1048576:
            memcache.add(sha, result, namespace='obj')
        return result

    def putobj(self, sha, value):
        if self.getobj(sha):
            # If already stored, don't create a duplicate
            return
        fn = files.blobstore.create(mime_type='application/octet-stream')
        f = files.open(fn, 'a')
        f.write(zlib.compress(value))
        f.close()
        files.finalize(fn)
        blobinfo = blobstore.get(files.blobstore.get_blob_key(fn))
        obj = Obj(key_name=sha, blob = blobinfo)
        obj.put()
        if len(value) < 1048576:
            memcache.add(sha, value, namespace='obj')

    def getstage(self):
        stage = Stage.get_by_key_name('stage')
        if stage is None:
            return None
        date = time.mktime(stage.date.timetuple())
        return {'parent': stage.parentcommit, 'tree': stage.tree, 'date': date}

    def putstage(self, stagedict):
        dt = datetime.datetime.fromtimestamp(stagedict['date'])
        stage = Stage(key_name='stage', parentcommit=stagedict['parent'], tree=stagedict['tree'], date=dt)
        stage.put()

    def getinforefs(self):
        q = Ref.all()
        result = {}
        for ref in q:
            name = ref.key().name()
            sha = ref.sha
            memcache.set(name, sha, namespace='ref')
            result[name] = sha
        return result

    # deprecated
    def setinforefs(self, inforefs):
        refs = []
        for name, sha in inforefs.iteritems():
            memcache.set(name, sha, namespace='ref')
            refs.append(Ref(key_name=name, sha=sha))
        db.put(refs)

    def getref(self, name):
        sha = memcache.get(name, namespace='ref')
        if sha: return sha
        ref = Ref.get_by_key_name(name)
        if ref:
            memcache.set(name, sha, namespace='ref')
            return ref.sha

    zerosha = '0' * 40

    # Return true on success
    def updateref(self, oldsha, newsha, name):
        # todo: make transactional
        oldref = Ref.get_by_key_name(name)
        if oldref:
            actual_oldsha = oldref.sha
        else:
            actual_oldsha = self.zerosha
        if actual_oldsha != oldsha:
            return False
        if newsha == self.zerosha:
            oldref.delete()
            memcache.delete(name, namespace='ref')
        else:
            newref = Ref(key_name=name, sha=newsha)
            newref.put()
            memcache.set(name, newsha, namespace='ref')
        return True

    def start_pack(self):
        return Blobwriter()
    def finish_pack(self, blobwriter, idx):
        blobinfo = blobwriter.close()
        idxblobwriter = Blobwriter()
        idxblobwriter.write(zlib.compress(idx))
        idxblob = idxblobwriter.close()
        pack = Pack(idx = idxblob, blob = blobinfo, date = datetime.datetime.now())
        pack.put()

    def getpacks(self):
        if self.packs is None:
            self.packs = []
            q = Pack.all()
            q.order('-date')
            for p in q.run(limit = 10):
                idxbytes = blobstore.BlobReader(p.idx).read()
                idx = json.decode(zlib.decompress(idxbytes))
                self.packs.append((idx, p.blob))
            logging.info("getpacks, len(packs) = " + `len(self.packs)`)
        return self.packs

    def get_obj_from_pack(self, sha):
        packs = self.getpacks()
        for idx, blob in packs:
            if idx.has_key(sha):
                off = idx[sha]
                reader = self.blobcache.open(blob, off)
                #logging.info('getting sha ' + sha + ' from ' + `off`)
                return self.get_pack_obj(reader, off)

class Blobwriter:
    def __init__(self):
        self.bs = []
    def write(self, bytes):
        self.bs.append(bytes)
    def close(self):
        fn = files.blobstore.create(mime_type='application/octet-stream')
        f = files.open(fn, 'a')
        # TODO: grouping into chunks would probably help optimize RPC's
        for b in self.bs:
            f.write(b)
        f.close()
        files.finalize(fn)
        return blobstore.get(files.blobstore.get_blob_key(fn))
