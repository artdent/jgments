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

import com.google.common.base.Objects;
import com.google.common.base.Preconditions;
import com.google.jgments.syntax.Token;

/** An annotation of a text span with a token type. */
public class SyntaxSpan {

  private final int startPos;
  private final int endPos;
  private final Token token;

  public SyntaxSpan(int startPos, int endPos, Token token) {
    this.startPos = startPos;
    this.endPos = endPos;
    this.token = Preconditions.checkNotNull(token);
  }

  public int getStartPos() {
    return startPos;
  }

  public int getEndPos() {
    return endPos;
  }

  public Token getToken() {
    return token;
  }

  @Override
  public String toString() {
    return String.format("%s [%s-%s)", token, startPos, endPos);
  }

  @Override
  public boolean equals(Object o) {
    if (o instanceof SyntaxSpan) {
      SyntaxSpan other = (SyntaxSpan) o;
      return other.startPos == startPos && other.endPos == endPos && other.token.equals(token);
    }

    return false;
  }

  @Override
  public int hashCode() {
    return Objects.hashCode(startPos, endPos, token);
  }
}
