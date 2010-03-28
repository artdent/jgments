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

"""Tool to create Java classes from Pygments lexers and token lists.

This tool aims to support most descendants of pygments.lexers.RegexLexer
that do not override get_tokens_unprocessed to do something fancy.
It requires a patched version of pygments that accepts the _record_only
attribute on RegexLexer instances.

Limitations:
- The using() token action does not support passing extra kwargs to
  the LanguageDefinition constructor.
- Regex modes other than multiline are not supported.
- The translation between Python and Java regular expressions is ad-hoc
  and imperfect. It might contain as-yet-undetected bugs.

The highest level interface to this module consists of the Write* functions
that output Java source code. The remaining non-private functions form the
slightly lower-level programmatic interface.

The command-line interface is usable standalone or via Blaze.
"""

import fnmatch
import os
import re
import sys

# Necessary for pygments import to work.
import google3.third_party.py.pygments.google
import mako.template
import pygments.lexer
import pygments.token

from google3.pyglib import iterlib
from google3.pyglib import resources

# NOTE(jacobly): more imports follow this monkeypatch call!


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
# We require the name attribute to be a valid Java identifier. "C++" is not.
pygments.lexers.compiled.CppLexer.name = 'Cpp'

# This list must be kept in sync with the BUILD rule.
# Note that lexer.name is sometimes capitalized non-obviously
# (e.g. 'JavaScript').
# TODO(jacobly): the commented-out lexers on this list are disabled due to
# regular expressions that this script cannot convert into valid Java regexes.
ALL_LEXERS = dict((lexer.name, lexer) for lexer in [
    #pygments.lexers.compiled.CLexer,
    pygments.lexers.compiled.CppLexer,
    #pygments.lexers.web.CssLexer,
    pygments.lexers.compiled.GoLexer,
    pygments.lexers.functional.HaskellLexer,
    #pygments.lexers.web.HtmlLexer,
    pygments.lexers.compiled.JavaLexer,
    pygments.lexers.web.JavascriptLexer,
    pygments.lexers.agile.PythonLexer,
    pygments.lexers.web.XmlLexer,
    ])

_DEFAULT_PACKAGE = 'com.google.jgments.syntax'
_DEFAULT_BASEDIR = 'third_party/java_src/jgments/java'
_TEMPLATES_DIR = 'google3/third_party/java_src/jgments/java/com/google/jgments'


def _EscapeForString(s):
  """Escape string contents for safe inclusion in a double-quoted string."""
  return s.replace('\\', '\\\\').replace('"', r'\"')


def _JavaLexerName(lexer_cls_name):
  """Return the name in Java of the given lexer class name."""
  assert ('.' not in lexer_cls_name,
          'Lexer class name must not refer to the enclosing module.')
  return lexer_cls_name + 'Syntax'


class _ProcessedTokenMatcher(object):
  """Translates token matcher tuples into Java syntax."""

  def __init__(self, matcher_tuple, lexer):
    """Parses and converts a token matcher tuple.

    Args:
      matcher_tuple: a tuple of the form (regex, token action, state action),
        with the last member being optional. This is the sort of tuple contained
        in the _tokens dictionary of a preprocessed RegexLexer subclass.
      lexer: the RegexLexer instance being processed.
    """
    if len(matcher_tuple) == 3:
      regex, token_action, state_action = matcher_tuple
    elif len(matcher_tuple) == 2:
      regex, token_action = matcher_tuple
      state_action = None
    else:
      raise RuntimeError('Wrong number of args in token matcher tuple %s'
                         % matcher_tuple)
    self._lexer = lexer
    self.regex = self._ProcessRegex(regex)
    self.token_action = self._ProcessTokenAction(token_action)
    self.state_action = self._ProcessStateAction(state_action)

  def __str__(self):
    return 'ProcessedTokenMatcher<%r, %r, %r>' % (
        self.regex, self.token_action, self.state_action)

  def _TokenRef(self, token):
    """Formats a Pygments token as a reference to a member of a Java enum."""
    return 'Token.' + _FormatToken(token)

  def _ProcessTokenAction(self, action):
    """Convert a token action into Java syntax."""
    if isinstance(action, pygments.lexer._TokenType):
      return 'TokenActions.singleToken(%s)' % (self._TokenRef(action,))
    elif isinstance(action, pygments.lexer.RegexLexerMeta):
      return '%s.INSTANCE' % _JavaLexerName(action.name)
    elif isinstance(action, tuple):
      fn, args = action
      if fn == 'using':
        assert len(args) == 1
        return self._ProcessUsing(args[0])
      elif fn == 'bygroups':
        return self._ProcessBygroups(args)
    raise RuntimeError('Unknown token action %s' % action)

  def _ProcessUsing(self, delegate):
    if delegate == pygments.lexer.this:
      return 'USING_THIS'
    else:
      return '%s.USING_THIS' % _JavaLexerName(delegate.name)

  def _ProcessBygroups(self, args):
    if iterlib.All(isinstance(arg, pygments.token._TokenType)
                   for arg in args):
      # Simple case: avoid the extra indirection when the action
      # for all groups is to yield a single token.
      args = [self._TokenRef(arg) for arg in args]
    else:
      args = [self._ProcessTokenAction(arg) for arg in args]
    # Capitalize "byGroups" per the Java convention.
    return 'TokenActions.byGroups(%s)' % ', '.join(args)

  def _ProcessLexerName(self, lexer_name):
    if lexer_name not in ALL_LEXERS:
      raise RuntimeError('No lexer available for %s' % lexer_name)
    return '"%s"' % lexer_name

  def _ProcessStateAction(self, action):
    """Converts a state transition action into Java syntax."""
    if not action:
      return 'StateActions.NOOP'
    elif isinstance(action, tuple):
      if len(action) == 1:
        # A 1-item tuple is the same as just performing the action itself.
        return self._ProcessStateAction(action[0])
      return 'StateActions.multiple(%s)' % ', '.join(
          self._ProcessStateAction(sub_action) for sub_action in action)
    elif isinstance(action, int):
      return 'StateActions.pop(%d)' % -action
    elif action == '#pop':
      return 'StateActions.pop(1)'
    elif action == '#push':
      return 'StateActions.DUPLICATE_TOP'
    elif isinstance(action, str):
      return 'StateActions.push(State.%s)' % _FormatState(action)
    raise RuntimeError('Unknown action %s' % action)

  def _ProcessRegex(self, regex):
    """Converts a regular expression to java syntax."""
    # Python regexes allow text like {foo}, but Java treats that as
    # "repeat the previous group foo times" and requires the {} to be escaped.
    regex = re.sub('{([^{}]*[^0-9,{}][^{}]*)}', r'\{\1\}', regex)
    # The same problem occurs for unbalanced special characters at the
    # beginning and end of a string.
    for open, close in zip('({[', ')}]'):
      regex = re.sub(r'\%s([^%s\\]+)$' % (open, close),
                     r'\%s\1' % open, regex)
      regex = re.sub(r'^([^%s\\]+)\%s' % (open, close),
                     r'\1\%s' % close, regex)
    # Python allows [ inside [], but Java requires escaping it if it is
    # not the first character in the class and if it is not already escaped.
    regex = re.sub(r'\[(.[^]]*)(?<!\\)\[([^]]*)\]', r'[\1\[\2]', regex)
    return _EscapeForString(regex)


def ExtractStates(lexer_cls):
  """Extracts the state dictionary from a pygments lexer class."""

  class RecordingLexer(lexer_cls):
    _record_only = True

  # Instantiating the lexer takes the tokens attribute, preprocesses it,
  # and produces a _tokens attribute that we can munge.
  lexer = RecordingLexer()

  states = {}
  for state, matchers in lexer._tokens.items():
    states[_FormatState(state)] = [
        _ProcessedTokenMatcher(matcher_tuple, lexer)
        for matcher_tuple in matchers]
  return states


def ConvertFilenames(filenames):
  """Converts a list of file name globs into single regex."""
  # The regexes returned by fnmatch.translate are simple enough that the
  # escaping used for token regexes is not necessary here.
  return _EscapeForString('(%s)$' % (
      '|'.join(fnmatch.translate(glob).rstrip('$') for glob in filenames)))


def AllTokens():
  """Retrieves all descendants of pygments.token.Token."""
  def Traverse(token):
    for tok in token.subtypes:
      yield tok
      for sub_token in Traverse(tok):
        yield sub_token
  return sorted(Traverse(pygments.token.Token))


def _FormatToken(token):
  """Converts a Pythonic token name into a Java-friendly constant name."""
  assert str(token).startswith('Token.'), 'Expected token, found ' + token
  return str(token)[len('Token.'):].replace('.', '_').upper()


def _FormatState(state):
  return state.replace('-', '_').upper()


def WriteTokens(config):
  """Converts the list of Pygments tokens into a Java enum.

  Args:
    config: an OutputConfiguration object.
  """
  outfile = config.OutputFile('Token')
  tokens = [_FormatToken(token) for token in AllTokens()]
  template = mako.template.Template(
      resources.GetResource(os.path.join(_TEMPLATES_DIR, 'tokens.mako')))
  outfile.write(template.render(tokens=tokens, package=config.package))


def WriteLexerList(config):
  """Writes the Java class containing the list of all lexers.

  Args:
    config: an OutputConfiguration object.
  """
  outfile = config.OutputFile('Lexers')
  template = mako.template.Template(
      resources.GetResource(os.path.join(_TEMPLATES_DIR, 'lexers.mako')))
  lexers = dict((name, _JavaLexerName(name)) for name in ALL_LEXERS)
  outfile.write(template.render(lexers=lexers, package=config.package))


def WriteLexer(config, name):
  """Converts a Pygments lexer into a Java lexer.

  Args:
    config: an OutputConfiguration object.
    name: the short name of the lexer (e.g. "Css" or "Python"),
      usable as an index into ALL_LEXERS.
  """
  try:
    lexer_cls = ALL_LEXERS[name]
  except KeyError:
    raise RuntimeError('Unknown lexer "%s"' % name)
  class_name = _JavaLexerName(name)
  outfile = config.OutputFile(class_name)
  states = ExtractStates(lexer_cls)
  filenames = ConvertFilenames(lexer_cls.filenames)
  template = mako.template.Template(
      resources.GetResource(os.path.join(_TEMPLATES_DIR, 'lexer.mako')))
  outfile.write(template.render(
      states=states, lexer_name=class_name, origin=lexer_cls,
      package=config.package, filenames=filenames))


class OutputConfiguration(object):
  """Configuration object describing where to write files.

  Attributes:
    package: package name for generated java files.
    basedir: directory to prepend to the package path.
    outfile: open file to write to. If None, a path will be derived
      from the other arguments.
  """

  def __init__(self, package=_DEFAULT_PACKAGE, basedir=_DEFAULT_BASEDIR,
               outfile=None):
    self.package = package
    self.basedir = basedir
    self.outfile = outfile
    self._written = False

  def OutputFile(self, class_name):
    """Returns an open file for writing the given class."""
    if self.outfile:
      if self._written:
        raise RuntimeError(
            'Attempted to write multiple classes to the same open file.')
      self._written = True
      return self.outfile
    return self._CreateParentsAndOpen(self._FilePath(class_name))

  def _CreateParentsAndOpen(self, path):
    """Opens a file for writing, recursively creating subdirs if needed."""
    directory = os.path.dirname(path)
    if not os.path.exists(directory):
      os.makedirs(directory)
    return open(path, 'w')

  def _FilePath(self, class_name):
    return os.path.join(self.basedir, self.package.replace('.', '/'),
                        class_name + '.java')


def main():
  if len(sys.argv) == 2:
    # With one argument, write a single module (either a lexer
    # or the token list) to stdout.
    config = OutputConfiguration(outfile=sys.stdout)
    if sys.argv[-1] == 'Tokens':
      WriteTokens(config)
    elif sys.argv[-1] == 'Lexers':
      WriteLexerList(config)
    else:
      WriteLexer(config, sys.argv[-1])
  elif len(sys.argv) == 1:
    # With no arguments, write all modules to the default output paths.
    config = OutputConfiguration()
    WriteTokens(config)
    for lexer_name in ALL_LEXERS:
      WriteLexer(config, lexer_name)
    WriteLexerList(config)
  else:
    raise RuntimeError('Unknown command line: ' + sys.argv)


if __name__ == '__main__':
  main()
