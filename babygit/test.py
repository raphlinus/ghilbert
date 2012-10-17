
import babygit
import repo
    
rootref = '03ae5eecc1935f3ab3af4c519a177044ce136181'
s = babygit.FsStore()
b = s.getobj(rootref)

def ls(store, sha, prefix = ''):
    r = repo.Repo(store)
    blob = store.getobj(sha)
    if blob is None:
        return
    t = babygit.obj_type(blob)
    if t == 'tree':
        for mode, name, child_sha in r.parse_tree(blob):
            print mode, prefix + '/' + name
            ls(store, child_sha, prefix + '/' + name)
