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
import com.google.jgments.syntax.LanguageDefinition;
import com.google.jgments.syntax.Token;

import java.util.List;
import java.util.regex.MatchResult;

/** Containing class for actions that yield tokens and manipulate the lexer position. */
public class TokenActions {

  private TokenActions() {}

  public interface Action {
    public List<SyntaxSpan> apply(MatchResult m, LexerState state);
  }

  /** Action that yields a single token in response to a matching regex. */
  public static final Action singleToken(final Token token) {
    return new Action() {
      public List<SyntaxSpan> apply(MatchResult m, LexerState state) {
        state.setPos(m.end());
        return ImmutableList.of(new SyntaxSpan(
            m.start() + state.getBasePos(), m.end() + state.getBasePos(), token));
      }
    };
  }

  /**
   * Action that delegates the lexing of a match result to another LanguageDefinition.
   *
   * TODO(jacobly): deprecate this method, since it is not compatible with the ability
   * to suspend and resume lexing.
   */
  public abstract static class UsingAction implements Action {
    /** Overrideable to specify which lexer to delegate to. */
    public abstract LanguageDefinition getLanguageDefinition();

    public List<SyntaxSpan> apply(MatchResult m, LexerState state) {
      LanguageDefinition other = getLanguageDefinition();
      LexerState subState = new LexerState(other.getRootState(), m.start() + state.getBasePos());
      RegexLexer delegate = new RegexLexer(other, m.group(), subState);
      return ImmutableList.copyOf(delegate);
    }
  }

  /** Composite action that applies a sub-action to each group in a match result. */
  public static Action byGroups(final Action ... actions) {
    return new Action() {
      public List<SyntaxSpan> apply(MatchResult m, LexerState state) {
        List<SyntaxSpan> ret = Lists.newArrayList();
        for (int i = 0; i < actions.length; i++) {
          SyntheticMatchResult innerMatch = new SyntheticMatchResult(m, i + 1);
          ret.addAll(actions[i].apply(innerMatch, state));
        }
        state.setPos(m.end());
        return ret;
      }
    };
  }

  /**
   * Action that yields one token per matching group in a regex.
   *
   * This is a special case of the bygroups action that accepts a list of actions;
   * it is implemented separately to avoid the performance hit of delegating to a
   * SingleToken action for the common case where the arguments to bygroups() consist only
   * of single tokens.
   * TODO(jacobly): benchmark to check if there is a meaningful performance difference.
   */
  public static Action byGroups(final Token ... tokens) {
    return new Action() {
      public List<SyntaxSpan> apply(MatchResult m, LexerState state) {
        List<SyntaxSpan> ret = Lists.newArrayList();
        for (int i = 0; i < tokens.length; i++) {
          String sub = m.group(i + 1);
          if (sub != null && sub.length() > 0) {
            state.setPos(m.start(i + 1));
            ret.add(new SyntaxSpan(
                m.start(i + 1) + state.getBasePos(), m.end(i + 1) + state.getBasePos(), tokens[i]));
          }
        }
        state.setPos(m.end());
        return ret;
      }
    };
  }
}
