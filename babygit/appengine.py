import hashlib
import logging
import zlib

from google.appengine.api import files
from google.appengine.ext import blobstore
from google.appengine.ext import db
from google.appengine.ext import webapp
from google.appengine.ext.webapp import blobstore_handlers

import store

class Obj(db.Model):
    # key is the sha hash
    blob = blobstore.BlobReferenceProperty(indexed=False)

class Ref(db.Model):
    # key is the refname (eg 'refs/heads/master')
    sha = db.StringProperty()

class AEStore(store.Store):
    def getlooseobj(self, sha):
        obj = Obj.get_by_key_name(sha)
        if not obj:
            return None
        buffer_size = min(1048576, obj.blob.size)
        blob_reader = blobstore.BlobReader(obj.blob, buffer_size = buffer_size)
        result = blob_reader.read()
        blob_reader.close()
        # Should we verify sha here? Could cost cpu...
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
