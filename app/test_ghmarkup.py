# encoding: utf-8

import unittest
import ghmarkup

class test_ghmarkup(unittest.TestCase):
  def test_unadorned_text(self):
    self.assertEqual("<p>\nfoo\n</p>", ghmarkup.ghmarkup("foo"))

  def test_bold(self):
    self.assertEqual("<p>\nthe <strong>quick</strong> brown fox\n</p>", ghmarkup.ghmarkup(
      "the *quick* brown fox"))

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

