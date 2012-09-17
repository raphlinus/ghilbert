# license

# Utilities for manipulating a repo. This layers on top of a store to provide
# raw object storage

import babygit

class Repo:
    def __init__(self, store):
        self.store = store
    def getroot(self):  # todo: handle more heads
        inforefs = self.store.getinforefs()
        obj = self.store.getobj(inforefs['refs/heads/master'])
        if babygit.obj_type(obj) != 'commit':
            raise ValueError('expected commit obj type')
        commitlines = obj[obj.find('\x00') + 1:].split('\n')
        for l in commitlines:
            if l.startswith('tree'):
                return l.split(' ')[1]
    def parse_tree(self, obj):
        if babygit.obj_type(obj) != 'tree': raise ValueError('wrong blob type')
        ix = obj.find('\x00') + 1
        if ix == 0: raise ValueError('missing nul')
        result = []
        while ix < len(obj):
            nul_ix = obj.find('\x00', ix)
            mode_and_name = obj[ix:nul_ix]
            mode, name = mode_and_name.split(' ', 1)
            sha = babygit.to_hex(obj[nul_ix + 1:nul_ix + 21])
            result.append((mode, name, sha))
            ix = nul_ix + 21
        return result
    def find_in_tree(self, parsed_tree, name):
        # Should be binary search
        for mode, n, sha in parsed_tree:
            if n == name:
                return mode, sha
