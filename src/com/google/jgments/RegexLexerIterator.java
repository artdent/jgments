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
import com.google.common.collect.Lists;
import com.google.common.collect.UnmodifiableIterator;
import com.google.jgments.syntax.LanguageDefinition;
import com.google.jgments.syntax.Token;

import java.util.List;
import java.util.regex.Matcher;

import javax.annotation.Nullable;

/** Iterator that generates a list of tokens for a text. */
public class RegexLexerIterator extends UnmodifiableIterator<SyntaxSpan> {

  private final LanguageDefinition lang;
  private final LexerState state;
  private final List<SyntaxSpan> annotationQueue;
  private final String text;

  public RegexLexerIterator(LanguageDefinition lang, String text, @Nullable LexerState state) {
    this.lang = lang;
    if (state != null) {
      this.state = state;
    } else {
      this.state = new LexerState(lang.getRootState());
    }
    annotationQueue = Lists.newArrayList();
    this.text = text;
  }

  public LexerState getState() {
    return state;
  }

  public boolean hasNext() {
    return state.getPos() < text.length() || !annotationQueue.isEmpty();
  }

  /**
   * {@inheritDoc}
   *
   * Scans farther in the text and returns a new token.
   * As a side effect, this advances the position, possibly changes the state stack,
   * and possibly finds and enqueues more tokens besides the one returned.
   */
  public SyntaxSpan next() {
    // If a match generated multiple tokens, yield them one at a time.
    if (!annotationQueue.isEmpty()) {
      return annotationQueue.remove(0);
    }

    // Find the first matching regex in the list of matchers for the current state.
    for (TokenMatcher tokenMatcher : lang.getStateTokenMatchers(state.top())) {
      Matcher m = tokenMatcher.getMatcher(text);
      m.region(state.getPos(), text.length());
      if (m.lookingAt()) {
        tokenMatcher.getStateAction().apply(state);
        annotationQueue.addAll(tokenMatcher.getTokenAction().apply(m, state));
        return annotationQueue.remove(0);
      }
    }

    /* If nothing matches at EOL, reset state to root. This is only relevant if we are given
     * a multiline string. */
    int currentPos = state.getPos();
    if (text.charAt(currentPos) == '\n') {
      state.setPos(currentPos + 1);
      state.reset(ImmutableList.of(lang.getRootState()));
      return new SyntaxSpan(currentPos, currentPos + 1, Token.TEXT);
    }

    state.setPos(currentPos + 1);
    return new SyntaxSpan(currentPos, currentPos + 1, Token.ERROR);
  }
}
