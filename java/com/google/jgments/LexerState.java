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

import com.google.common.annotations.VisibleForTesting;
import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.base.Splitter;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.jgments.syntax.LanguageDefinition;
import com.google.jgments.syntax.LanguageDefinition.State;

import java.util.ArrayList;
import java.util.List;

/**
 * Holds the state of the lexer.
 * This state has two components: a stack of the current states, and the current position inside
 * the text.
 *
 * TODO(jacobly): this class could be split: stack is only used by StateActions objects,
 * and pos and basePos are only used by TokenActions objects.
 */
public class LexerState {
  private final List<State> stack;
  private int pos;
  private final int basePos;

  public LexerState(State initialState) {
    this(initialState, 0);
  }

  public LexerState(State initialState, int basePos) {
    // LinkedList is the more traditional data structure for a stack, but ArrayList has better
    // performance with a small number of elements, and typically the state stack contains
    // only a handful of entries.
    stack = Lists.newArrayList();
    push(initialState);
    this.basePos = basePos;
  }

  /** Returns the current state (i.e. the top of the state stack). */
  public State top() {
    return stack.get(0);
  }

  /**
   * Returns the state stack.
   * This method is only for testing, since how the states are stored is an implementation detail.
   */
  @VisibleForTesting
  List<State> getStack() {
    return stack;
  }

  /** Resets the state stack. */
  public void reset(List<State> newState) {
    stack.clear();
    stack.addAll(newState);
  }

  /** Pushes a state onto the stack. */
  public void push(State state) {
    stack.add(0, Preconditions.checkNotNull(state));
  }

  /** Pops 1 or more states from the stack. */
  public void pop(int n) {
    // The root state should not be popped.
    Preconditions.checkState(stack.size() - n >= 1);
    for (int i = 0; i < n; i++) {
      stack.remove(0);
    }
  }

  /** Duplicates the current topmost state. */
  public void duplicateTop() {
    push(stack.get(0));
  }

  // TODO(jacobly): move position management into RegexLexerIterator.
  public void setPos(int pos) {
    this.pos = pos;
  }

  public int getPos() {
    return pos;
  }

  /**
   * Returns the amount of offset that must be added to getPos() to determine
   * the real position in the original string.
   * This amount is non-zero when a lexer is being applied to a substring,
   * as is the case when the lexer is invoked by TokenActions.using().
   */
  public int getBasePos() {
    return basePos;
  }

  /** Serializes a LexerState as a string. */
  public String serialize() {
    List<String> fields = new ArrayList<String>();
    for (State st : stack) {
      fields.add(st.toString());
    }
    fields.add(Integer.toString(basePos));
    fields.add(Integer.toString(pos));
    return Joiner.on(",").join(Iterables.reverse(fields));
  }

  /**
   * Deserializes a LexerState.
   *
   * @param serialized the string containing the serialized LexerState object
   * @param lang a LanguageDefinition instance that can reconstruct serialized states
   */
  public static LexerState deserialize(String serialized, LanguageDefinition lang) {
    List<String> fields = ImmutableList.copyOf(Splitter.on(",").split(serialized));
    Preconditions.checkState(fields.size() >= 3);
    int pos = Integer.parseInt(fields.get(0));
    int basePos = Integer.parseInt(fields.get(1));
    // The root state is stored at the beginning and the topmost state at the end.
    LexerState state = new LexerState(lang.deserializeState(fields.get(2)), basePos);
    state.setPos(pos);
    for (int i = 3; i < fields.size(); i++) {
      state.push(lang.deserializeState(fields.get(i)));
    }
    return state;
  }
}
