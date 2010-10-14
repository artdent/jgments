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

import com.google.jgments.syntax.LanguageDefinition;

/** Containing class for actions that manipulate the lexer state stack. */
public class StateActions {

  private StateActions() {}

  public interface Action {
    public void apply(LexerState state);
  }

  /** Action that does nothing. */
  public static final Action NOOP = new Action() {
    public void apply(LexerState state) { }
  };

  /** Action that duplicates the top state on the stack. */
  public static final Action DUPLICATE_TOP = new Action() {
    public void apply(LexerState state) {
      state.duplicateTop();
    }
  };

  // Static instance for the Pop action that is the most common by far.
  // TODO(jacobly): determine whether this is a significant memory savings.
  private static final Action POP = new Action() {
    public void apply(LexerState state) {
      state.pop(1);
    }
  };

  /** Action that pops the topmost state from the stack. */
  public static Action pop(final int numLevels) {
    if (numLevels == 1) {
      return POP;
    }
    return new Action() {
      public void apply(LexerState state) {
        state.pop(numLevels);
      }
    };
  }

  /** Composite action that applies other actions in sequence. */
  public static Action multiple(final Action... actions) {
    return new Action() {
      public void apply(LexerState state) {
        for (Action action : actions) {
          action.apply(state);
        }
      }
    };
  }

  /** Action that pushes a new state onto the stack. */
  public static Action push(final LanguageDefinition.State stateName) {
    return new Action() {
      public void apply(LexerState state) {
        state.push(stateName);
      }
    };
  }
}
