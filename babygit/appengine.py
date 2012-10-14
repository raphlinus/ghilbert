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

import store

class Obj(db.Model):
    # key is the sha hash
    blob = blobstore.BlobReferenceProperty(indexed=False)

class Pack(db.Model):
    idx = blobstore.BlobReferenceProperty(indexed=False)
    blob = blobstore.BlobReferenceProperty(indexed=False)

class Ref(db.Model):
    # key is the refname (eg 'refs/heads/master')
    sha = db.StringProperty()

class Stage(db.Model):
    # the key should probably be the userid
    parentcommit = db.StringProperty()
    tree = db.StringProperty()
    date = db.DateTimeProperty(auto_now=True)

class AEStore(store.Store):
    def getobj(self, sha, verify = False):
        obj = memcache.get(sha, namespace='obj')
        if obj is not None:
            return obj
        result = self.getobjimpl(sha, verify)
        if result and len(result) < 1048576:
            memcache.add(sha, result, namespace='obj')
        return result

    def getlooseobj(self, sha):
        obj = Obj.get_by_key_name(sha)
        if not obj:
            return None
        buffer_size = min(1048576, obj.blob.size)
        blob_reader = blobstore.BlobReader(obj.blob, buffer_size = buffer_size)
        result = blob_reader.read()
        blob_reader.close()
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
            result[ref.key().name()] = ref.sha
        return result
    def setinforefs(self, inforefs):
        refs = []
        for ref, sha in inforefs.iteritems():
            refs.append(Ref(key_name=ref, sha=sha))
        db.put(refs)

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
        else:
            newref = Ref(key_name=name, sha=newsha)
            newref.put()
        return True

