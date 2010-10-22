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

"""Module for rewriting regular expressions in a target language.

Usage:
  >>> import youstillhavetwoproblems
  >>> youstillhavetwoproblems.to_java('{I got 99 problems}')
  '\\{I got 99 problems\\}'

This module works by translating the output of the internal sre_parse module.
The output of to_python is not guaranteed to match the input: for example,
characters that are allowed to be escaped may be escaped even if they
were not escaped in the input string.

It is guaranteed, though, that every valid regular expression will be
translated into an equivalent regex valid for the target language.

Disclaimer: Some more obscure constructions have not been tested
and may or may not have been implemented yet.

You might still have two problems, but at least one of them
won't be translating regular expressions from Python to Java.
"""

import string
import sys
import sre_parse


CATEGORIES = {}
for escape_seq, (op, av) in sre_parse.CATEGORIES.items():
  if op == 'in':
    CATEGORIES[av[0][1]] = escape_seq
ESCAPES = dict((chr(value), key)
               for key, (op, value) in sre_parse.ESCAPES.items())
SAFE = string.letters + string.digits + ' ";'


class Renderer(object):
  """Language-neutral (but basically Pythonic) base renderer."""

  def __call__(self, pattern):
    return self._render(sre_parse.parse(pattern))

  def _render(self, pattern_obj):
    return ''.join([self.op(op, av) for op, av in pattern_obj])

  def escape(self, av, in_char_class):
    if av >= 128:
      return unichr(av)
    s = chr(av)
    if s in ESCAPES:
      return ESCAPES[s]
    if in_char_class and s in '-[]':
      # This escaping is (usually) optional at the first character
      # in the class, but it is easier to simply always escape.
      return '\\' + s
    if not in_char_class and s not in SAFE:
      return '\\' + s
    return s

  def op(self, op, av):
    try:
      renderer = getattr(self, 'op_' + op)
    except AttributeError:
      raise NotImplementedError(op)
    return renderer(av)

  def op_in(self, av):
    ret = []
    for op, a in av:
      if op == 'negate':
        ret.append('^')
      elif op == 'literal':
        ret.append(self.escape(a, True))
      elif op == 'range':
        ret.append('%s-%s' % (self.escape(a[0], True), self.escape(a[1], True)))
      elif op == 'category':
        ret.append(CATEGORIES[a])
    return '[%s]' % ''.join(ret)

  def op_literal(self, av):
    return self.escape(av, False)

  def op_subpattern(self, av):
    group_num, pattern = av
    if not group_num:
      return '(?:%s)' % self._render(pattern)
    return '(%s)' % self._render(pattern)

  def op_branch(self, av):
    return '|'.join(self._render(a) for a in av[1])

  def op_assert(self, av):
    direction, pattern = av
    if direction == 1:
      return '(?=%s)' % self._render(pattern)
    return '(?<=%s)' % self._render(pattern)

  def op_assert_not(self, av):
    direction, pattern = av
    if direction == 1:
      return '(?!%s)' % self._render(av[1])
    return '(?<!%s)' % self._render(pattern)

  def op_max_repeat(self, av):
    lower, upper, pattern = av
    pattern_ret = self._render(pattern)
    if lower == 0 and upper == 1:
      return pattern_ret + '?'
    elif lower == 0 and upper == sre_parse.MAXREPEAT:
      return pattern_ret + '*'
    elif lower == 1 and upper == sre_parse.MAXREPEAT:
      return pattern_ret + '+'
    elif upper == sre_parse.MAXREPEAT:
      return '%s{%d,}' % (pattern_ret, lower)
    elif lower == upper:
      return '%s{%d}' % (pattern_ret, lower)
    return '%s{%d,%d}' % (pattern_ret, lower, upper)

  def op_min_repeat(self, av):
    return self.op_max_repeat(av) + '?'

  def op_any(self, av):
    return '.'

  def op_at(self, av):
    return {'at_beginning': '^',
            'at_end': '$',
            'at_boundary': '\\b',
            'at_non_boundary': '\\B'}[av]

  def op_not_literal(self, av):
    return '[^%s]' % self.escape(av, True)

  def op_groupref(self, av):
    return '\\%d' % av


class JavaRenderer(Renderer):
  # Java regexes are not 100% compatible with Python: for example, [ab[cd] and
  # {foo} are legal in Python but not Java. However, all the examples I have
  # come across can be rendered in a way that is compatible with both languages.
  # (The above examples would be [ab\[cd] and \{foo\}). So this implementation
  # is vacuous... for now.
  pass


class JavascriptRenderer(Renderer):

  def op_assert(self, av):
    direction, pattern = av
    if direction == -1:
      raise NotImplementedError('Lookbehind is not supported in Javascript')
    return super(JavascriptRenderer, self).op_assert(av)

  def op_assert_not(self, av):
    direction, pattern = av
    if direction == -1:
      raise NotImplementedError('Lookbehind is not supported in Javascript')
    return super(JavascriptRenderer, self).op_assert_not(av)


to_python = Renderer()
to_java = JavaRenderer()
to_javascript = JavascriptRenderer()
