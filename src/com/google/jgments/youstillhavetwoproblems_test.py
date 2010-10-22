#!/usr/bin/python2.4
#
# Copyright 2010 Google Inc.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are
# met:
#
#     * Redistributions of source code must retain the above copyright
# notice, this list of conditions and the following disclaimer.
#     * Redistributions in binary form must reproduce the above
# copyright notice, this list of conditions and the following disclaimer
# in the documentation and/or other materials provided with the
# distribution.
#     * Neither the name of Google Inc. nor the names of its
# contributors may be used to endorse or promote products derived from
# this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
# OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
# SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
# LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
# DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
# THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

import sre_constants
import unittest
try:
  from google3.third_party.java_src.jgments.java.com.google.jgments import (
      youstillhavetwoproblems)
except ImportError:
  import youstillhavetwoproblems


class TestRegularExpressionRendering(unittest.TestCase):

  def check(self, src, dest=None):
    if not dest:
      dest = src
    self.assertEqual(dest, youstillhavetwoproblems.to_python(src))

  def testRegexes(self):
    self.check('foo')
    self.check('[a-bc-dz]')
    self.check('[^a-bc-dz]')
    self.check('[^a]')
    self.check(r'[+\-*/]')
    self.check('[]]', r'\]')
    self.check('[]a]', r'[\]a]')
    self.check('[[]', r'\[')
    self.check('[[a]', r'[\[a]')
    self.check('[[a-]', r'[\[a\-]')
    self.check('(foo)')
    self.check('(foo|bar)foo|bar|baz')
    self.check('^foo$')
    self.check('foo{3,5}')
    self.check('f.*a?b+o')
    self.check('f.*?a??b+?o')
    self.check('foo{3}')
    self.check('foo{3,}')
    self.check('foo{3,}?')
    self.check('foo{3,5}?')
    self.check('{foo}', r'\{foo\}')
    self.check(u'\u0234[\u0235\u0236]', u'\u0234[\u0235\u0236]')
    self.check(r'foo(a)(b)\1\2')
    self.check(r'\d\n[ab\d\n]', r'[\d]\n[ab\d\n]')
    self.check('(?=foo)(?<=foo)(?:foo)')
    self.check('(?!foo)(?<!foo)')
    self.assertRaises(NotImplementedError,
                      youstillhavetwoproblems.to_javascript, '(?<!foo)')
    self.assertRaises(sre_constants.error,
                      youstillhavetwoproblems.to_python, '(foo')

if __name__=='__main__':
  unittest.main()
