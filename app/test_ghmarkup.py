# encoding: utf-8

import unittest
import ghmarkup

class test_ghmarkup(unittest.TestCase):
  def test_unadorned_text(self):
    self.assertEqual("""<p>
foo
</p>""", ghmarkup.ghmarkup("foo"))

  def test_bold(self):
    self.assertEqual("""<p>
the <strong>quick</strong> brown fox
</p>""", ghmarkup.ghmarkup("the **quick** brown fox"))

  def test_italics(self):
    self.assertEqual("""<p>
However, it is not a <em>metric</em> space.
</p>""", ghmarkup.ghmarkup("However, it is not a _metric_ space."))

  def test_italics_via_slashes(self):
    self.assertEqual("""<p>
, which implies our result. <em>Here we are using the compactness of S.</em>
</p>""", ghmarkup.ghmarkup(", which implies our result. //Here we are using the compactness of S.//"))

  def test_asterisk(self):
    self.assertEqual("""<p>
We find *3.42 more helpful than *7.82 here.
</p>""", ghmarkup.ghmarkup("We find *3.42 more helpful than *7.82 here."))

  def test_bullet(self):
    self.assertEqual("""<ul>
<li>
<div>
one
</div>
</li>
</ul>""", ghmarkup.ghmarkup("* one"))

  def test_two_bullets(self):
    self.assertEqual("""<ul>
<li>
<div>
one
</div>
</li>
<li>
<div>
two
</div>
</li>
</ul>""", ghmarkup.ghmarkup("* one\n* two\n"))

  def test_no_blank_line_before_bullet(self):
    self.assertEqual("""<p>
Animals:
</p>
<ul>
<li>
<div>
dog
</div>
</li>
</ul>""", ghmarkup.ghmarkup("Animals:\n* dog"))

  def test_math(self):
    self.assertEqual(u'<p>\n<span class="sexp">(→ p q)</span>\n</p>', ghmarkup.ghmarkup("#(→ p q)#"))

  def test_literal(self):
    self.assertEqual(u'<p>\n<tt>#(→ p q)#</tt>\n</p>', ghmarkup.ghmarkup("{{{#(→ p q)#}}}"))

if __name__ == '__main__':
    unittest.main()

