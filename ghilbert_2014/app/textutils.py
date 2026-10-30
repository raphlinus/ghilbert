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

# Utilities for processing text files, including patching and diffing,
# as well as semantic splitting of ghilbert proof files.

def count_char(line, ch, limit):
    count = 0
    i = 0
    while True:
        i = line.find(ch, i, limit)
        if i < 0: return count
        count += 1
        i += 1

def count_parens(line):
    limit = line.find('#')
    if limit == -1: limit = len(line)
    return count_char(line, '(', limit) - count_char(line, ')', limit)

def tokenize(line):
    line = line.split('#')[0]
    line = line.replace('(', ' ( ')
    line = line.replace(')', ' ) ')
    return line.split()

# Returns a list of (name, (startline, endline)) tuples, where lines are
# 0-based, and exclusive of endline. Ignore comment blocks for now
# Splits gh and ghi files.
def split_gh_file(lines):
    level = 0
    result = []
    startline = 0
    name = None
    for i, line in enumerate(lines):
        delta = count_parens(line)
        if level == 0 and name is None:
            if line.startswith('#!'):
                startline = i + 1
            elif startline == i and line.rstrip() == '':
                startline = i + 1
            else:
                toks = tokenize(line)
                if len(toks) >= 3 and toks[0] in ('thm', 'defthm', 'stmt') and toks[1] == '(':
                    name = toks[2]
                elif level + delta == 0 and len(toks) and toks[-1] == ')':
                    startline = i + 1
        level += delta
        if name is not None and level == 0:
            result.append((name, (startline, i + 1)))
            name = None
            startline = i + 1
    return result

# for testing
if __name__ == '__main__':
    import sys
    lines = file(sys.argv[1]).read().split('\n')
    annot = split_gh_file(lines)
    print annot
    ix = 0
    pref = ''
    for i, line in enumerate(lines):
        if ix < len(annot) and i == annot[ix][1][1]:
            pref = ''
            ix += 1
        if ix < len(annot) and i == annot[ix][1][0]:
            pref = annot[ix][0] + ':'
        print '%10s %s' % (pref, line)

