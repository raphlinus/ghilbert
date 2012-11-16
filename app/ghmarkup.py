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

# A formatter for Ghilbert's special brand of wiki formatting.

import re

def htmlquote(s):
    s = s.replace('&', '&amp;')
    s = s.replace('<', '&lt;')
    s = s.replace('>', '&gt;')
    return s

def urlquote(s):
    s = s.replace('"', '%22')
    return s

def urlquoteplus(s):
    s = urlquote(s)
    s = s.replace('+', '%2b')
    s = s.replace(' ', '+')
    return s

def wikiwhat(page):
    basepage = page
    if page.endswith('/talk'): basepage = page[:-5]
    if basepage.find('/') >= 0:
        return page
    else:
        return 'wiki/' + page

# Decide whether a given "what" lives in theorem space
def thmspace(what):
    lwhat = what.split('/')
    return len(lwhat) > 1 and lwhat[-1] != 'talk' and lwhat[0] not in ('wiki', 'bib', 'user')

def wikiexists(page):
    what = wikiwhat(page)
    if what in ('wiki/RecentChanges',): return True
    return False  # for now, we'll wire up the database soon
    if thmspace(what):
        return Log.objects.filter(what=what+'/_thm').count() > 0 or Log.objects.filter(what=what+'/_stmt').count() > 0
    else:
        return Log.objects.filter(what=what).count() > 0

def userlink(uname, body = None):
    return '[user links not supported yet]'
    try:
        user = User.objects.get(username=uname)
    except:
        return '[deleted account ' + uname + ']'
    try:
        profile = UserProfile.objects.get(user=user.id)
    except:
        return '[deleted account ' + uname + ']'
    realname = ''
    if profile.otro_lang != settings.LANGUAGE_CODE[:2] and lang_suffix[1:]==profile.otro_lang:
        realname = (profile.otro_first_name+" "+profile.otro_last_name).decode('utf-8')
        realname = ''.join(map(lambda x: '&#%d;' % (ord(x)),realname))
    if realname=='':
        realname = (profile.first_name+" "+profile.last_name).decode('utf-8')
        realname = ''.join(map(lambda x: '&#%d;' % (ord(x)),realname))
    if body == None:
        body = realname
    return '<a class="user" href="' + i18n_base + '/user/' + uname + '">' + body + '</a>'

def wikilink(str, path='', exists = None, ispreblock = False, ctx = None):
    ctx = parse_url_path(path)
    pos = str.rfind('->')
    if pos >= 0:
        body = str[:pos].rstrip()
        link = str[pos + 2:].lstrip()
    else:
        linkl = str.split('|', 1)
        if len(linkl) == 2:
            link = linkl[0].rstrip()
            body = linkl[1].lstrip()
        else:
            link, = linkl
            body = None
    aclass = ''
    if re.match(r'[a-z0-9\.\+]*://', link):
        url = linktext = link
    elif re.match(r'user/[^/]+$', link):
        return userlink(link[5:], body)
    else:
        linktext = link
        if ctx and link.find('/') < 0: link = ctx + '/' + link
        if exists or (exists == None and wikiexists(link)):
            aclass = 'class="wiki" '
        else:
            aclass = 'class="new" '
        if str == '' and body == None:
            body = 'wiki home page'
        url = wikiurl(link)
    langtext = ''
    if body == None:
        if re.match('wiki/', linktext):
            body = linktext[5:]
        elif re.match('bib/', linktext):
            body = '[' + linktext[4:] + ']'
        else:
            body = linktext
    return '<a ' + aclass + 'href="' + urlquote(url) + '">' + htmlquote(body) + langtext+'</a>'

def wikiurl(page):
    wikipath = wikiwhat(page)
    if wikipath.startswith('/'):
        return wikipath
    else:
        return '/' + wikipath

def wikigh(str, ispreblock):
    return '<span class="sexp">' + htmlquote(str) + '</span>'

def wikipre(str, ispreblock):
    if ispreblock:
        return '<pre>' + htmlquote(str) + '</pre>'
    else:
        return '<tt>' + htmlquote(str) + '</tt>'

class ListState:
    ltags = {':': ('<blockquote>', '<p>'),
             '*': ('<ul>', '<div>'),
             '#': ('<ol>', '<div>')}
    def __init__(self):
        self.state = ''
    def begblock(self, result, bullet, tag = ''):
        i = min(len(self.state), len(bullet))
        if len(bullet) and len(bullet) == len(self.state):
            i -= 1
        newstate = self.state[:i] + bullet[i:]
        if len(bullet): tag = self.ltags[bullet[-1]][1]
        if len(bullet) == len(self.state) and bullet.endswith(':'):
            tag = '<p>'
            newstate = newstate[:-1] + self.state[-1]
        elif self.state.endswith('*') or self.state.endswith('#'):
            result.append('</li>')
        j = i
        if j < len(newstate) and j < len(self.state):
            if newstate[j] == self.state[j]: j += 1
        for c in reversed(self.state[j:]):
            result.append(self.ltags[c][0].replace('<', '</'))
        for c in newstate[j:]:
            result.append(self.ltags[c][0])
        if bullet.endswith('*') or bullet.endswith('#'):
            result.append('<li>')
        if tag != '':
            result.append(tag)
        self.state = newstate
        if tag != '': return tag.replace('<', '</')

def parse_url_path(path):
    if path.find('/')>0:
        ctx = path.rsplit('/',1)[0]
        if ctx=='wiki':
            ctx=''
    else:
        ctx = ''
    return ctx

def process_ghmarkup(str, path):
    if not isinstance(str, unicode):
        str = unicode(str, 'utf-8')
    eol_re = re.compile(r'\r?\n')
    blank_re = re.compile(r'\s*$')
    rule_re = re.compile(r'\s*\-{4,}\s*$')
    bullet_re = re.compile(r'([:\*#]+)\s+')
    head_re = re.compile(r'(={2,6})\s*')
    special_re = re.compile(r'''
        [<>&\\] |          # HTML entities and backslash
        (?<!-)---?(?!-) |  # en and em dash, exactly 2 or 3 hyphens
        (?<!:)// |         # begin italic markup, but avoid URL's
        \*\* |             # begin bold markup
        \[\[ |             # open link
        \{\{\{ |           # open preformatted
        (?<![^\s\"\(])     # single char markup must follow whitespace
          ([#_\*\[])
          (?=\S)           # and not be followed by whitespace
        ''', re.VERBOSE)
    repls = {'<': '&lt;', '>': '&gt;', '&': '&amp;',
             '--': '&#x2013;', '---': '&#x2014;'}
    emphs = {'_': 'i', '*' : 'b', '//': 'em', '**': 'strong'}
    def my_wikilink(str, ispreblock = False):
        return wikilink(str, path, ispreblock = False)
    embeds = {'[': (r'\]', my_wikilink), '[[': (r'\]\]', my_wikilink), 
              '#': (r'#', wikigh),
              '{{{': (r'\}\}\}(?!\})', wikipre)}
    for open, (close, embedfn) in embeds.items():
        embeds[open] = (re.compile(close), embedfn)
    result = []
    pclose = None
    stack = []
    liststate = ListState()
    lines = eol_re.split(str) + ['']
    i = 0
    while i < len(lines):
        line = lines[i]
        i += 1
        if pclose in ('</div>', None):
            bullet_m = bullet_re.match(line)
        else:
            bullet_m = None
        if pclose != None and (blank_re.match(line) or bullet_m):
            if stack:
                stack.reverse()
                result.append(''.join([htmlclose for wikiclose, htmlclose in stack]))
                stack = []
            result.append(pclose)
            pclose = None
        elif pclose == None and rule_re.match(line):
            liststate.begblock(result, '', '<hr />')
            continue
        if blank_re.match(line): continue
        if pclose == None:
            head_m = head_re.match(line)
            if bullet_m:
                bullet = bullet_m.group(1)
                pclose = liststate.begblock(result, bullet_m.group(1))
                pos = bullet_m.end()
            elif head_m:
                delim = head_m.group(1)
                pclose = liststate.begblock(result, '', '<h%d>' % len(delim))
                stack.append((delim, ''))
                pos = head_m.end()
            else:
                pclose = liststate.begblock(result, '', '<p>')
                pos = 0
        else:
            pos = 0
        rline = ''
        while pos < len(line):
            m = special_re.search(line, pos)
            if len(stack):
                # Handle closing tags for inline markup
                pos2 = line.find(stack[-1][0], pos)
                if pos2 >= 0 and (not m or pos2 <= m.start()):
                    rline += line[pos:pos2] + stack[-1][1]
                    pos = pos2 + len(stack[-1][0])
                    del stack[-1]
                    continue
            if m:
                rline += line[pos:m.start()]
                g = m.group()
                mend = m.end()
                if repls.has_key(g):
                    rline += repls[g]
                    pos = mend
                elif emphs.has_key(g):
                    rline += '<' + emphs[g] + '>'
                    stack.append((g, '</' + emphs[g] + '>'))
                    pos = mend
                elif g in embeds:
                    wikiclose, embedfn = embeds[g]
                    sline, spos = i - 1, mend
                    ispreblock = g == '{{{' and mend == 3 and blank_re.match(line, 3)
                    while sline < len(lines):
                        end_m = wikiclose.search(lines[sline], spos)
                        if end_m and ispreblock and (end_m.start() != 0 or
                                          not blank_re.match(lines[sline], 3)):
                            end_m = None
                        if end_m:
                            break
                        sline, spos = sline + 1, 0
                    if end_m:
                        if sline == i - 1:
                            str = line[mend:end_m.start()]
                        else:
                            str = line[mend:] + '\n'
                            for j in range(i, sline):
                                str += lines[j] + '\n'
                            str += lines[sline][:end_m.start()]
                        rline += embedfn(str, ispreblock = ispreblock)
                        i = sline + 1
                        line = lines[sline]
                        pos = end_m.end()
                        continue
                elif g == '\\':
                    if mend < len(line) and line[mend] in '\\{}_#[]*-/':
                        rline += line[mend]
                        pos = mend + 1
                if pos < mend:
                    # Nothing matched above, pass verbatim.
                    rline += g
                    pos = mend
            else:
                rline += line[pos:]
                break
        result.append(rline)
    liststate.begblock(result, '')
    return '\n'.join(result)

def ghmarkup(value, path = ''):
    return process_ghmarkup(value, path)

def talklink(value,path=''):
    (i18n_base, ctx, lang_suffix) = parse_url_path(path)
    if re.search(r'/_norm', value): value = value[:-6]
    if re.search(r'/talk', value):
        return wikilink(value[:-5] + '|'+_('Main page'),path)
    else:
        return wikilink(value + '/talk|'+_('Discuss'),path)

def translatelink(value, what = None):
    if value != what:
        return 'edit/'+urlquote(what)
    return 'edit/'+urlquote(value)

