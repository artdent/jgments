// Copyright 2010 Google Inc. All Rights Reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
//     * Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above
// copyright notice, this list of conditions and the following disclaimer
// in the documentation and/or other materials provided with the
// distribution.
//     * Neither the name of Google Inc. nor the names of its
// contributors may be used to endorse or promote products derived from
// this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

package com.google.jgments;

import com.google.common.collect.ImmutableList;
import com.google.jgments.TokenActions.Action;
import com.google.jgments.syntax.PythonSyntax;
import com.google.jgments.syntax.PythonSyntax.State;
import com.google.jgments.syntax.Token;

import junit.framework.TestCase;

import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/** Tests for token-yielding actions. */
public class TokenActionsTest extends TestCase {

  public void testSingleToken() {
    Action action = TokenActions.singleToken(Token.COMMENT);
    LexerState state = new LexerState(State.ROOT);
    Matcher matcher = Pattern.compile("test").matcher("a test text");
    assertTrue(matcher.find());
    assertEquals(0, state.getPos());

    List<SyntaxSpan> outcome = ImmutableList.copyOf(action.apply(matcher, state));
    assertEquals(6, state.getPos());
    assertEquals(1, outcome.size());
    assertEquals(new SyntaxSpan(2, 6, Token.COMMENT), outcome.get(0));
  }

  public void testBygroups() {
    Action action = TokenActions.byGroups(Token.KEYWORD, Token.COMMENT, Token.LITERAL_NUMBER);
    LexerState state = new LexerState(State.ROOT);
    Matcher matcher = Pattern.compile("(te)(s)(t)").matcher("a test text");
    assertTrue(matcher.find());
    assertEquals(0, state.getPos());

    List<SyntaxSpan> outcome = ImmutableList.copyOf(action.apply(matcher, state));
    assertEquals(6, state.getPos());
    assertEquals(3, outcome.size());
    assertEquals(new SyntaxSpan(2, 4, Token.KEYWORD), outcome.get(0));
    assertEquals(new SyntaxSpan(4, 5, Token.COMMENT), outcome.get(1));
    assertEquals(new SyntaxSpan(5, 6, Token.LITERAL_NUMBER), outcome.get(2));
  }

  public void testBygroupsUsing() {
    Action action = TokenActions.byGroups(
        TokenActions.singleToken(Token.PUNCTUATION),
        PythonSyntax.USING_THIS,
        TokenActions.singleToken(Token.PUNCTUATION));
    LexerState state = new LexerState(State.ROOT);
    Matcher matcher = Pattern.compile("(\\[)(def a\\(\\): pass)(\\])extra").matcher(
        "[def a(): pass]extra");
    assertTrue(matcher.find());

    List<SyntaxSpan> outcome = ImmutableList.copyOf(action.apply(matcher, state));
    assertEquals(20, state.getPos());
    assertEquals(10, outcome.size());
    assertEquals(new SyntaxSpan(0, 1, Token.PUNCTUATION), outcome.get(0));
    assertEquals(new SyntaxSpan(1, 4, Token.KEYWORD), outcome.get(1));
    assertEquals(new SyntaxSpan(4, 5, Token.TEXT), outcome.get(2));
    assertEquals(new SyntaxSpan(5, 6, Token.NAME_FUNCTION), outcome.get(3));
    assertEquals(new SyntaxSpan(6, 7, Token.PUNCTUATION), outcome.get(4));
    assertEquals(new SyntaxSpan(7, 8, Token.PUNCTUATION), outcome.get(5));
    assertEquals(new SyntaxSpan(8, 9, Token.PUNCTUATION), outcome.get(6));
    assertEquals(new SyntaxSpan(9, 10, Token.TEXT), outcome.get(7));
    assertEquals(new SyntaxSpan(10, 14, Token.KEYWORD), outcome.get(8));
    assertEquals(new SyntaxSpan(14, 15, Token.PUNCTUATION), outcome.get(9));
  }
}
