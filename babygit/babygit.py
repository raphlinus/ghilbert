import hashlib
import os
import struct
import zlib

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
    if src_size != len(ref): raise ValueError('size mismatch')
    result_size, offset = get_delta_hdr_size(delta, offset)
    size_remaining = result_size
    result = []
    while offset < len(delta):
        oo = offset
        cmd = ord(delta[offset])
        offset += 1
        if cmd & 0x80:
            # copy from reference
            copy_off = 0
            copy_size = 0
            for i in range(4):
                if cmd & (1 << i):
                    copy_off |= ord(delta[offset]) << (i << 3)
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

class FsStore:
    def __init__(self, basedir = '.git'):
        self.basedir = basedir
        self.packs = None
    def getblob(self, sha):
        path = os.path.join(self.basedir, 'objects', sha[:2], sha[2:])
        if os.path.exists(path):
            f = file(path)
            blob = zlib.decompress(f.read())
        else:
            return self.get_blob_from_packs(sha)
        if hashlib.sha1(blob).hexdigest() != sha:
            print 'shas don\'t match'
        return blob
    def getpacks(self):
        if self.packs is None:
            self.packs = self.readpacks()
        return self.packs
    def readpacks(self):
        packs = []
        packpath = os.path.join(self.basedir, 'objects', 'pack') 
        for fn in os.listdir(packpath):
            if fn.endswith('.idx'):
                idx = file(os.path.join(packpath, fn)).read()
                packfn = os.path.join(packpath, fn[:-4] + '.pack')
                packs.append((idx, packfn))
        return packs
    def get_blob_from_packs(self, sha):
        print 'fetching', sha, 'from pack'
        firstbyte = int(sha[:2], 16)
        binaryhash = from_hex(sha)
        for idx, fn in self.getpacks():
            if firstbyte == 0:
                indexlo = 0
                indexhi, = struct.unpack('>I', idx[8:12])
            else:
                off = 4 + 4 * firstbyte
                indexlo, indexhi = struct.unpack('>II', idx[off:off+8])
            # Now try to find exact hash
            # todo: replace linear with binary or interpolation search
            found_ix = None
            for ix in range(indexlo, indexhi):
                off = 1032 + 20 * ix
                if idx[off:off+20] == binaryhash:
                    found_ix = ix
                    break
            if found_ix is not None:
                n_objs, = struct.unpack('>I', idx[1028:1032])
                off = 1032 + 24 * n_objs + 4 * found_ix
                pack_off, = struct.unpack('>I', idx[off:off + 4])
                print 'found, ix =', ix, 'pack_off =', pack_off
                return self.get_pack_blob(fn, pack_off)
    def read_zlib(self, f, size):
        result = []
        d = zlib.decompressobj()
        sizeremaining = size
        while sizeremaining > 0:
            block = d.decompress(f.read(16))
            result.append(block)
            sizeremaining -= len(block)
        return ''.join(result)
    def get_pack_blob(self, packfn, offset):
        f = file(packfn)
        f.seek(offset)
        t, size = self.get_type_and_size(f)
        if t < 5:
            return self.read_zlib(f, size)
        elif t == 6:  # OBJ_OFS_DELTA
            byte = ord(f.read(1))
            off = byte & 0x7f
            while byte & 0x80:
                byte = ord(f.read(1))
                off = ((off + 1) << 7) + (byte & 0x7f)
            ref_offset = offset - off
            delta = self.read_zlib(f, size)
            ref = self.get_pack_blob(packfn, ref_offset)
            return patch_delta(ref, delta)
        elif t == 7:  # OBJ_REF_DELTA
            ref_sha = to_hex(f.read(20))
            print ref_sha
            delta = self.read_zlib(f, size)
            return patch_delta(self.getblob(ref_sha), delta)
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

def blob_type(blob):
    return blob[:4]

def to_hex(binary_data):
    return ''.join(['%02x' % ord(x) for x in binary_data])

def from_hex(hex_data):
    n = len(hex_data) >> 1
    return struct.pack(n * 'B', *[int(hex_data[i*2:i*2+2], 16) for i in range(n)])

def parse_tree(blob):
    if blob_type(blob) != 'tree': raise ValueError('wrong blob type')
    ix = blob.find('\x00') + 1
    if ix == 0: raise ValueError('missing nul')
    result = []
    while ix < len(blob):
        nul_ix = blob.find('\x00', ix)
        mode_and_name = blob[ix:nul_ix]
        mode, name = mode_and_name.split(' ', 1)
        sha = to_hex(blob[nul_ix + 1:nul_ix + 21])
        result.append((mode, name, sha))
        ix = nul_ix + 21
    return result

rootref = '03ae5eecc1935f3ab3af4c519a177044ce136181'
s = FsStore()
b = s.getblob(rootref)

def ls(store, sha, prefix = ''):
    blob = store.getblob(sha)
    if blob is None:
        return
    t = blob_type(blob)
    if t == 'tree':
        for mode, name, child_sha in parse_tree(blob):
            print prefix + '/' + name
            ls(store, child_sha, prefix + '/' + name)

ls(s, rootref)
