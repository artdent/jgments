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

"""Import and monkeypatch the Pygments lexers."""

# Suppress warnings about unusual import order.
# pylint: disable-msg=C6204,C6205,W0611
try:
  # Necessary for pygments import to work in google3.
  import google3.third_party.py.pygments.google
except ImportError:
  pass

import pygments.lexer


def _MonkeypatchTokenizerHelpers(module, func_names):
  """Replaces preprocessor functions.

  Pygments defines some functions that are called when a lexer is constructed,
  returning opaque objects that we can't inspect. We must replace those objects
  with ones that simply note the name of the function called.
  For example, instead of calling bygroups (which returns a matcher function),
  we must note that bygroups is called at that point.

  Args:
    module: the module to patch.
    func_names: the list of function names in that module to replace.
  """
  def _MakeRecorder(func_name):
    # Ignore the keyword args, which we don't support.
    return lambda *args, **kwargs: (func_name, args)
  for func_name in func_names:
    getattr(module, func_name)  # First make sure the function exists.
    setattr(module, func_name, _MakeRecorder(func_name))

_MonkeypatchTokenizerHelpers(pygments.lexer, ['bygroups', 'using'])

# Import the modules we are capable of extracting.
import pygments.lexers.agile
import pygments.lexers.compiled
import pygments.lexers.functional
import pygments.lexers.web
# We require the name attribute to be a valid Java identifier.
pygments.lexers.agile.Python3Lexer.name = 'Python3'
pygments.lexers.compiled.CppLexer.name = 'Cpp'
pygments.lexers.compiled.ObjectiveCLexer.name = 'ObjectiveC'

# This list must be kept in sync with the BUILD rule.
# Note that lexer.name is sometimes capitalized non-obviously
# (e.g. 'JavaScript').
ALL = dict((lexer.name, lexer) for lexer in [
    pygments.lexers.compiled.CLexer,
    pygments.lexers.compiled.CppLexer,
    pygments.lexers.web.CssLexer,
    pygments.lexers.compiled.GoLexer,
    pygments.lexers.functional.HaskellLexer,
    pygments.lexers.web.HtmlLexer,
    pygments.lexers.compiled.JavaLexer,
    pygments.lexers.web.JavascriptLexer,
    pygments.lexers.compiled.ObjectiveCLexer,
    pygments.lexers.agile.PerlLexer,
    pygments.lexers.agile.PythonLexer,
    pygments.lexers.agile.Python3Lexer,
    pygments.lexers.compiled.ScalaLexer,
    pygments.lexers.web.XmlLexer,
    ])
