#!/usr/bin/python
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

The command-line interface is usable standalone or via the Google build system.
"""

import fnmatch
import os
import re
import sys

# Suppress warnings about unusual import order.
# pylint: disable-msg=C6204,C6205,W0611
try:
  import google3
  from google3.third_party.java_src.jgments.java.com.google.jgments import (
      lexers, youstillhavetwoproblems)
  from google3.pyglib import iterlib
  from google3.pyglib import resources
except ImportError:
  google3 = None
  import lexers
  import youstillhavetwoproblems
  from stubs import iterlib
  from stubs import resources

import mako.template
# Import pygments after the lexers module does its monkeypatching.
import pygments.formatters.html
import pygments.lexer
import pygments.token
assert pygments.lexer.bygroups.__module__ == 'lexers', 'Pygments was not monkeypatched!'

_DEFAULT_PACKAGE = 'com.google.jgments.syntax'
if google3:
  _DEFAULT_BASEDIR = 'third_party/java_src/jgments/java'
  _TEMPLATES_DIR = 'google3/%s/com/google/jgments' % _DEFAULT_BASEDIR
else:
  _DEFAULT_BASEDIR = 'build/java'
  _TEMPLATES_DIR = 'java/com/google/jgments'


def _EscapeForString(s):
  """Escape string contents for safe inclusion in a double-quoted string."""
  return s.replace('\\', '\\\\').replace('"', r'\"')


def _JavaLexerName(lexer_cls_name):
  """Return the name in Java of the given lexer class name."""
  assert '.' not in lexer_cls_name, \
      'Lexer class name must not refer to the enclosing module.'
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
    if lexer_name not in lexers.ALL:
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
    return _EscapeForString(youstillhavetwoproblems.to_java(regex))


class _RecordingLexerMeta(pygments.lexer.RegexLexerMeta):

  def _process_regex(cls, regex, rflags):
    return regex

  def _process_token(cls, token):
    return token


def ExtractStates(lexer_cls):
  """Extracts the state dictionary from a pygments lexer class."""

  class RecordingLexer(lexer_cls):
    __metaclass__ = _RecordingLexerMeta

  # Instantiating the lexer takes the tokens attribute, preprocesses it,
  # and produces a _tokens attribute that we can munge.
  lexer = RecordingLexer()

  states = {}
  for state, matchers in lexer._tokens.items():
    states[_FormatState(state)] = [
        _ProcessedTokenMatcher(matcher_tuple, lexer)
        for matcher_tuple in matchers]
  return states


def _GlobToRegex(glob):
  """Converts a shell glob to a regular expression."""
  # fnmatch.translate adds '$' or '\Z(?ms)' (on python >= 2.6)
  # to the end of the regex.
  return fnmatch.translate(glob).rstrip('$').replace(r'\Z(?ms)', '')


def ConvertFilenames(filenames):
  """Converts a list of file name globs into single regex."""
  # The regexes returned by fnmatch.translate are simple enough that the
  # escaping used for token regexes is not necessary here.
  return _EscapeForString('(%s)$' % (
      '|'.join(_GlobToRegex(glob) for glob in filenames)))


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
  all_tokens = AllTokens()
  tokens = [_FormatToken(token) for token in all_tokens]
  short_names = [pygments.formatters.html._get_ttype_class(token)
                 for token in all_tokens]
  template = mako.template.Template(
      resources.GetResource(os.path.join(_TEMPLATES_DIR, 'tokens.mako')))
  outfile.write(template.render(tokens=tokens, short_names=short_names,
                                package=config.package))


def WriteLexerList(config):
  """Writes the Java class containing the list of all lexers.

  Args:
    config: an OutputConfiguration object.
  """
  outfile = config.OutputFile('Lexers')
  template = mako.template.Template(
      resources.GetResource(os.path.join(_TEMPLATES_DIR, 'lexers.mako')))
  lexer_list = dict((name, _JavaLexerName(name)) for name in lexers.ALL)
  outfile.write(template.render(lexers=lexer_list, package=config.package))


def WriteLexer(config, name):
  """Converts a Pygments lexer into a Java lexer.

  Args:
    config: an OutputConfiguration object.
    name: the short name of the lexer (e.g. "Css" or "Python"),
      usable as an index into ALL_LEXERS.
  """
  try:
    lexer_cls = lexers.ALL[name]
  except KeyError:
    raise RuntimeError('Unknown lexer "%s"' % name)
  class_name = _JavaLexerName(name)
  outfile = config.OutputFile(class_name)
  states = ExtractStates(lexer_cls)
  filenames = ConvertFilenames(lexer_cls.filenames)
  template = mako.template.Template(
      resources.GetResource(os.path.join(_TEMPLATES_DIR, 'lexer.mako')))
  outfile.write(template.render_unicode(
      states=states, lexer_name=class_name, origin=lexer_cls,
      package=config.package, filenames=filenames).encode('utf-8'))


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
    for lexer_name in lexers.ALL:
      WriteLexer(config, lexer_name)
    WriteLexerList(config)
  else:
    raise RuntimeError('Unknown command line: ' + sys.argv)


if __name__ == '__main__':
  main()
