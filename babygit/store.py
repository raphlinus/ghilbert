# license

import hashlib
import zlib

# This is a handy base class for actual store implementations to derive from.

# Note: this is not done yet, as it needs more thinking about how to handle
# pack reading

obj_types = [None, 'commit', 'tree', 'blob', 'tag']

def get_delta_hdr_size(data, offset):
    byte = ord(data[offset])
    offset += 1
    size = byte & 0x7f
    shift = 7
    while byte & 0x80:
        byte = ord(data[offset])
        offset += 1
        size += (byte & 0x7f) << shift
        shift += 7
    return size, offset

def patch_delta(ref, delta):
    src_size, offset = get_delta_hdr_size(delta, 0)
    data_off = ref.find('\x00') + 1
    if src_size != len(ref) - data_off: raise ValueError('size mismatch')
    result_size, offset = get_delta_hdr_size(delta, offset)
    size_remaining = result_size
    result = [obj_type(ref) + ' ' + str(result_size) + '\x00']
    while offset < len(delta):
        oo = offset
        cmd = ord(delta[offset])
        offset += 1
        if cmd & 0x80:
            # copy from reference
            copy_off = data_off
            copy_size = 0
            for i in range(4):
                if cmd & (1 << i):
                    copy_off += ord(delta[offset]) << (i << 3)
                    offset += 1
            for i in range(3):
                if cmd & (0x10 << i):
                    copy_size |= ord(delta[offset]) << (i << 3)
                    offset += 1
            if copy_size == 0: copy_size = 0x10000
            if copy_off + copy_size > len(ref):
                raise ValueError('size overflow')
            if copy_size > size_remaining:
                raise ValueError('output size overflow')
            result.append(ref[copy_off:copy_off + copy_size])
            size_remaining -= copy_size
        elif cmd > 0:
            if cmd > size_remaining: raise ValueError('output size overflow')
            result.append(delta[offset:offset + cmd])
            offset += cmd
            size_remaining -= cmd
        else:
            raise ValueError('caught zero command')
    if size_remaining: raise ValueError('didn\'t fill output buffer')
    return ''.join(result)

class Store:
    # This is the usual public api. An actual store can override this.
    def getobj(self, sha, verify = False):
        return self.getobjimpl(sha, verify)

    def getobjimpl(self, sha, verify):
        raw = self.get_obj_from_pack(sha)
        if raw is None:
            compressed = self.getlooseobj(sha)
            if compressed:
                raw = zlib.decompress(compressed)
            else:
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

    # The following methods are provided as convenience for stores that
    # read (standard) packfiles

    def read_zlib(self, f, size):
        result = []
        d = zlib.decompressobj()
        sizeremaining = size
        while sizeremaining > 0:
            block = d.decompress(f.read(4096))
            result.append(block)
            sizeremaining -= len(block)
        return ''.join(result)
    def get_pack_obj(self, f, offset):
        f.seek(offset)
        t, size = self.get_type_and_size(f)
        if t < 5:
            hdr = obj_types[t] + ' ' + str(size) + '\x00'
            return hdr + self.read_zlib(f, size)
        elif t == 6:  # OBJ_OFS_DELTA
            byte = ord(f.read(1))
            off = byte & 0x7f
            while byte & 0x80:
                byte = ord(f.read(1))
                off = ((off + 1) << 7) + (byte & 0x7f)
            ref_offset = offset - off
            delta = self.read_zlib(f, size)
            ref = self.get_pack_obj(packfn, ref_offset)
            return patch_delta(ref, delta)
        elif t == 7:  # OBJ_REF_DELTA
            ref_sha = binascii.hexlify(f.read(20))
            #print ref_sha
            delta = self.read_zlib(f, size)
            return patch_delta(self.getobj(ref_sha), delta)
        else:
            print 'can\'t handle type =', t
    def get_type_and_size(self, f):
        byte = ord(f.read(1))
        t = (byte >> 4) & 7
        size = byte & 15
        shift = 4
        while byte & 0x80:
            byte = ord(f.read(1))
            size += (byte & 0x7f) << shift
            shift += 7
        return (t, size)
