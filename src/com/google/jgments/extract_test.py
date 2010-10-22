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

"""Unit tests for the pygments extraction code."""

import os

# Suppress warnings about unusual import order.
# pylint: disable-msg=C6204,C6205,W0611
try:
  import google3
  # It is necessary to import extract before importing
  # pygments modules, otherwise the monkeypatching doesn't work.
  from google3.third_party.java_src.jgments.java.com.google.jgments import (
      extract)
  from google3.pyglib import flags
  from google3.testing.pybase import googletest
  TestCase = googletest.TestCase
except ImportError:
  google3 = None
  import extract
  import stubs
  import unittest

  class TestCase(unittest.TestCase, stubs.TestCaseHelpers):
    pass

import pygments.lexer
import pygments.lexers.agile
import pygments.lexers.compiled
import pygments.token

PythonLexer = pygments.lexers.agile.PythonLexer


class RecordingPythonLexer(PythonLexer):
  __metaclass__ = extract._RecordingLexerMeta


class ExtractTest(TestCase):

  def setUp(self):
    if google3:
      self.outdir = flags.FLAGS.test_tmpdir
    else:
      self.outdir = 'build/test-output/tmp'

  def testFormatToken(self):
    self.assertEqual('TEXT', extract._FormatToken(pygments.token.Text))
    self.assertEqual('LITERAL_STRING',
                     extract._FormatToken(pygments.token.Literal.String))
    self.assertEqual('NAME_VARIABLE_CLASS',
                     extract._FormatToken(pygments.token.Name.Variable.Class))

  def testAllTokens(self):
    all_tokens = extract.AllTokens()
    self.assertNotIn(pygments.token.Token, all_tokens)
    self.assertIn(pygments.token.Text, all_tokens)
    # Lexers are free to add to the defined tokens, so there might be
    # more tokens in all_tokens than in the list of standard tokens
    # depending on which lexers were imported.
    self.assertTrue(len(all_tokens + [pygments.token.Token])
                    >= len(pygments.token.STANDARD_TYPES))

  def testMonkeypatching(self):
    self.assertEqual(('bygroups', ('a', 'b')),
                     pygments.lexer.bygroups('a', 'b'))
    self.assertEqual(('using', ('a', 'b')),
                     pygments.lexer.using('a', 'b'))
    self.assertEqual(('using', ('a', 'b')),
                     pygments.lexer.using('a', 'b', random_option=True))
    self.assertEqual('Cpp', pygments.lexers.compiled.CppLexer.name)

  def testFilePath(self):
    config = extract.OutputConfiguration(package='java.com.google',
                                         basedir='jgments')
    self.assertEqual('jgments/java/com/google/Test.java',
                     config._FilePath('Test'))

  def testExtractStates(self):
    states = extract.ExtractStates(PythonLexer)
    # Test some things that are likely not to change when pygments is upgraded.
    self.assertIn('ROOT', states)
    self.assertIn('IMPORT', states)

  def testProcessedTokenMatcher(self):
    matcher = (r'"fo\\o"', pygments.token.Comment)
    processed = extract._ProcessedTokenMatcher(matcher, None)
    self.assertEqual(r'\"fo\\\\o\"', processed.regex)
    self.assertEqual('TokenActions.singleToken(Token.COMMENT)',
                     processed.token_action)
    self.assertEqual('StateActions.NOOP', processed.state_action)

    matcher = (r'foo', pygments.token.Comment, (-1,))
    processed = extract._ProcessedTokenMatcher(matcher, None)
    self.assertEqual('StateActions.pop(1)', processed.state_action)

    matcher = (r'foo', pygments.token.Comment, ('root', 'import'))
    processed = extract._ProcessedTokenMatcher(matcher, None)
    self.assertEqual('StateActions.multiple(StateActions.push(State.ROOT), '
                     'StateActions.push(State.IMPORT))',
                     processed.state_action)

  def testProcessedTokenMatcher_Bygroups(self):
    matcher = (r'"f(oo)(bar)"', ('bygroups', (pygments.token.Comment,
                                              pygments.token.String)))
    processed = extract._ProcessedTokenMatcher(matcher, None)
    self.assertEqual(
        'TokenActions.byGroups(Token.COMMENT, Token.LITERAL_STRING)',
        processed.token_action)

  def testProcessedTokenMatcher_Using(self):
    matcher = (r'"f(oo)(bar)"', ('bygroups', (pygments.token.Comment,
                                              ('using', (PythonLexer,)),
                                              pygments.token.String)))
    processed = extract._ProcessedTokenMatcher(matcher, None)
    self.assertEqual(
        'TokenActions.byGroups(TokenActions.singleToken(Token.COMMENT), '
        'PythonSyntax.USING_THIS, '
        'TokenActions.singleToken(Token.LITERAL_STRING))',
        processed.token_action)

  def testProcessedTokenMatcher_UsingThis(self):
    matcher = (r'"f(oo)(bar)"', ('using', (pygments.lexer.this,)))
    processed = extract._ProcessedTokenMatcher(matcher, RecordingPythonLexer())
    self.assertEqual('USING_THIS', processed.token_action)

  def testRegexConversion(self):
    dummy = extract._ProcessedTokenMatcher(('', pygments.token.Comment), None)
    def Check(transformed, initial):
      self.assertEqual(transformed, dummy._ProcessRegex(initial))
    Check('foo', 'foo')
    Check(r'f\"o\"\\\\o', r'f"o"\\o')
    # Various nasty character classes that contain punctuation.
    Check(r'[\\]{}:(),;\\[]', '[]{}:(),;[]')
    Check(r'\\[', r'[\[]')
    Check(r'\\[', '[[]')
    Check(r'[\\]\\[a]', '[][a]')
    Check('(a)', '(a)')
    Check(r'\\{foo.*\\}', '{foo.*}')
    Check(r'\\{foo3foo\\}', '{foo3foo}')
    Check('foo{1,2}bar{1,3}', r'foo{1,2}bar{1,3}')
    Check('a{3}', 'a{3}')
    Check('a{3,5}', 'a{3,5}')
    Check(r'foobar\\{baz', 'foobar{baz')
    Check(r'foobar\\]baz', 'foobar]baz')
    Check(r'foo\\)barbaz', r'foo\)barbaz')
    Check(r'\\(', r'\(')
    Check(r'\\n', r'\n')

  def testConvertFilenames(self):
    self.assertEqual(r'(.*\\.py|.*\\.pyw|.*\\.sc|SConstruct|SConscript)$',
                     extract.ConvertFilenames(PythonLexer.filenames))
    self.assertEqual('([^ab-e].*f.o)$',
                     extract.ConvertFilenames(['[!ab-e]*f?o']))

  def _ConfigForTest(self):
    return extract.OutputConfiguration(basedir=self.outdir, package='com.foo')

  def testWriteTokens(self):
    extract.WriteTokens(self._ConfigForTest())
    output = open(os.path.join(self.outdir,
                               'com', 'foo', 'Token.java')).read()
    self.assertIn('package com.foo;', output)
    self.assertIn('public enum Token {', output)
    self.assertIn('COMMENT,', output)

  def testWriteLexer(self):
    extract.WriteLexer(self._ConfigForTest(), 'Python')
    output = open(os.path.join(self.outdir,
                               'com', 'foo', 'PythonSyntax.java')).read()
    self.assertIn('package com.foo;', output)
    self.assertIn('public class PythonSyntax '
                  'extends AbstractLanguageDefinition<PythonSyntax.State> {',
                  output)
    self.assertIn('singleToken(Token.LITERAL_STRING_INTERPOL),', output)

  def testWriteLexerList(self):
    extract.WriteLexerList(self._ConfigForTest())
    output = open(os.path.join(self.outdir,
                               'com', 'foo', 'Lexers.java')).read()
    self.assertIn('package com.foo;', output)
    self.assertIn('public class Lexers {', output)
    self.assertIn('ALL', output)
    self.assertIn('PythonSyntax', output)


if __name__ == '__main__':
  if google3:
    googletest.main()
  else:
    unittest.main()
