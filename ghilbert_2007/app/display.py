# Display a mathematical layout, using x3

import sys

import x3
import typeset
import verify # remove

def my_callback(cmd, what, arg, more):
    if cmd == 'abou':
        popup_about()
    elif cmd == 'save':
        do_save()
    else:
        print cmd, what, arg

class x3page:
    def __init__(self):
        self.ftab = {}
        self.content = []
    def read_font(self, fontname, font_fn):
        print 'read_font', fontname, font_fn
        self.ftab[fontname] = font_fn
    def clear(self):
        self.content = []
    def write_slug_nl(self, slug):
        self.content.append(slug.markup)

class display_view:
    def __init__(self, page):
        self.page = page
        self.zoom = 1.6
    def draw_markup(self, dc, markup):
        #print markup
        if markup[0] == 'glyph':
            #print 'font file', self.page.ftab[markup[1]]
            dc.selectfontfile(self.page.ftab[markup[1]], 0)
            dc.setfontsize(int(markup[2]) * self.zoom)
            if markup[3][0] == 'u' and markup[3][1] == '+':
                c = unichr(int(markup[3][2:], 16))
                #c = c.encode('utf8')
            else:
                c = chr(int(markup[3]))
            dc.showtext(c)
        elif markup[0] == 'string':
            #print 'font file', self.page.ftab[markup[1]]
            dc.selectfontfile(self.page.ftab[markup[1]], 0)
            dc.setfontsize(int(markup[2]) * self.zoom)
            dc.showtext(markup[3])
        elif markup[0] == 'hbox':
            for child in markup[1:]:
                self.draw_markup(dc, child)
        elif markup[0] == 'vbox':
            for i in range(1, len(markup) - 1, 2):
                x, y = dc.currentpoint()
                self.draw_markup(dc, markup[i])
                y += int(markup[i + 1]) * self.zoom
                dc.moveto(x, y)
            self.draw_markup(dc, markup[-1])
        elif markup[0] == 'rise':
            x, y = dc.currentpoint()
            dc.moveto(x, y - int(markup[1]) * self.zoom)
            self.draw_markup(dc, markup[2])
            x1, y1 = dc.currentpoint()
            dc.moveto(x1, y)
        elif markup[0] == 'sp':
            x, y = dc.currentpoint()
            x += int(markup[1]) * self.zoom
            dc.moveto(x, y)
    def draw(self, dc):
        dc.setrgba(1, 1, 1, 1)
        dc.rectangle(*dc.rect)
        dc.fill()
        dc.setrgba(0, 0, 0, 1)
        y = 12 * self.zoom
        for markup in self.page.content:
            dc.moveto(10, y)
            self.draw_markup(dc, markup)
            x, y = dc.currentpoint()
            y += 12 * self.zoom
    def clear(self):
        self.page.clear()
    def add_wff(self, wff):
        typeset.print_term(self.page, wff)
    def add_term(self, term):
        typeset.print_term(self.page, term[1], term[0])
    def add_status(self, status):
        self.page.write_slug_nl(typeset.markup_slug(['string', 'ghr10', '10', status]))
    def dirty(self):
        self.view.dirty()

if __name__ == '__main__':
    script = file(sys.argv[1])
    page = x3page()
    typeset.read_script(page, script)

    win = x3.window(0, "math display test", my_callback)
    v = display_view(page)
    x3.view(win, 0x100, v)
    x3.main()
