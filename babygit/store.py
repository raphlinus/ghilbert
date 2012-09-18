# license

import hashlib
import zlib

# This is a handy base class for actual store implementations to derive from.

# Note: this is not done yet, as it needs more thinking about how to handle
# pack reading

obj_types = [None, 'commit', 'tree', 'blob', 'tag']

class Store:
    # This is the usual public api. An actual store can override this.
    def getobj(self, sha, verify = False):
        return self.getobjimpl(sha, verify)

    def getobjimpl(self, sha, verify):
        compressed = self.getlooseobj(sha)
        if compressed:
            raw = zlib.decompress(compressed)
        else:
            raw = self.get_obj_from_pack(sha)
            if raw is None:
                return None
        if verify:
            if hashlib.sha1(raw).hexdigest() != sha:
                raise ValueError('shas don\'t match')
        return raw

    def getobjz(self, sha):
        compressed = self.getlooseobj(sha)
        if compressed:
            return compressed
        # If the obj in a pack is not a delta, then an optimization would be
        # to not decompress and recompress it. But not done yet.
        raw = self.get_obj_from_pack(sha)
        return zlib.compress(raw)
        
    # Everything is expected to implement getlooseobj at a minimum. It
    # returns zlib compressed objects.

    def get_obj_from_pack(self, sha):
        pass

    def put(self, t, data):
        raw = t + ' ' + str(len(data)) + '\x00' + data
        sha = hashlib.sha1(raw).hexdigest()
        self.putobj(sha, raw)
        return sha
