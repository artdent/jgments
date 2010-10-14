<%def name="format_matcher(token_matcher)" filter="trim">
new TokenMatcher(
                "${token_matcher.regex}",
                ${token_matcher.token_action},
                ${token_matcher.state_action})
</%def>
## The below comment applies to the generated source, not to this Mako template.
// Autogenerated -- Do not edit!
// Origin: ${origin.__module__}.${origin.__name__}.
// Generated by extract.py for Jgments:
//   http://s/?fileprint=//depot/google3/third_party/java_src/java/com/google/jgments/extract.py.

package ${package};

import com.google.jgments.TokenActions;
import com.google.jgments.TokenMatcher;
import com.google.jgments.StateActions;
import com.google.jgments.syntax.Token;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;

public class ${lexer_name} extends AbstractLanguageDefinition<${lexer_name}.State> {
  public enum State implements LanguageDefinition.State {
    % for state in states.keys()[:-1]:
      ${state},
    % endfor
      ${states.keys()[-1]}
  }

  public State getRootState() {
    return State.ROOT;
  }

  @Override
  protected Class<State> getStateClass() {
    return State.class;
  }

  @Override
  protected String getFileNamePattern() {
    return "${filenames}";
  }

  public static final TokenActions.Action USING_THIS = new TokenActions.UsingAction() {
    @Override
    public LanguageDefinition getLanguageDefinition() {
      return INSTANCE;
    }
  };

  public static final LanguageDefinition INSTANCE = new ${lexer_name}();

  public ${lexer_name}() {
    super(new ImmutableMap.Builder<State, ImmutableList<TokenMatcher>>()
    % for state, token_matchers in states.items():
        .put(State.${state}, new ImmutableList.Builder<TokenMatcher>()
        % for token_matcher in token_matchers:
            .add(${format_matcher(token_matcher)})
        % endfor
            .build()
        )
    % endfor
        .build());
  }
}