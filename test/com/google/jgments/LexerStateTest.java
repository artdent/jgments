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
import com.google.jgments.LexerState;
import com.google.jgments.syntax.PythonSyntax;

import junit.framework.TestCase;

public class LexerStateTest extends TestCase {

  public void testSerialize() {
    LexerState state = new LexerState(PythonSyntax.State.ROOT, 10);
    assertEquals("0,10,ROOT", state.serialize());
    state.setPos(30);
    state.push(PythonSyntax.State.SQS);
    assertEquals("30,10,ROOT,SQS", state.serialize());
  }

  public void testDeserialize() {
    PythonSyntax lexer = new PythonSyntax();
    LexerState state = LexerState.deserialize("30,10,ROOT,SQS", lexer);
    assertEquals(30, state.getPos());
    assertEquals(10, state.getBasePos());
    assertEquals(ImmutableList.of(PythonSyntax.State.SQS, PythonSyntax.State.ROOT),
        state.getStack());
    assertEquals(PythonSyntax.State.SQS, state.top());
    state.pop(1);
    assertEquals(PythonSyntax.State.ROOT, state.top());
  }
}
