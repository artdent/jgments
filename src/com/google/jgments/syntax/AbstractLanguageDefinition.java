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

package com.google.jgments.syntax;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;

import com.google.jgments.TokenMatcher;

import java.util.EnumMap;
import java.util.List;
import java.util.regex.Pattern;

/**
 * Abstract implementation of LanguageDefinition.
 *
 * Concrete implementations of this class are automatically generated from Pygments classes.
 * Their public constructor calls the protected LanguageDefinition constructor
 * with a hard-coded dictionary of TokenMacher objects.
 * Made-up example:
 *
 * <pre>
 * public class MyLanguageSyntax extends LanguageDefinitionImpl<MyLanguageSyntax.State> {
 *   public MyLanguageSyntax() {
 *     super(new ImmutableMap.Builder<String, ImmutableList<TokenMatcher>>()
 *         .put(State.ROOT, ImmutableList.of(
 *             new TokenMatcher(
 *                 "\"",
 *                 TokenActions.singleToken(Token.LITERAL_STRING),
 *                 StateActions.pop(1)),
 *             new TokenMatcher(
 *                 "#",
 *                 TokenActions.singleToken(COMMENT),
 *                 StateActions.NOOP)
 *          )).build();
 *   }
 * }
 * </pre>
 */
public abstract class AbstractLanguageDefinition<ST extends Enum<ST> & LanguageDefinition.State>
    implements LanguageDefinition {
  /** The mapping of state to a list of matchers applicable in that state. */
  protected final EnumMap<ST, ImmutableList<TokenMatcher>> states;

  private final Pattern compiledFileNamePattern;

  protected abstract Class<ST> getStateClass();

  protected abstract String getFileNamePattern();

  protected AbstractLanguageDefinition(ImmutableMap<ST, ImmutableList<TokenMatcher>> states) {
    this.states = new EnumMap<ST, ImmutableList<TokenMatcher>>(states);
    this.compiledFileNamePattern = Pattern.compile(getFileNamePattern());
  }

  public State deserializeState(String stateName) {
    return Enum.valueOf(getStateClass(), stateName);
  }

  public boolean isApplicable(String fileName) {
    return compiledFileNamePattern.matcher(fileName).matches();
  }

  public List<TokenMatcher> getStateTokenMatchers(State state) {
    return states.get(state);
  }
}
