## The below comment applies to the generated source, not to this Mako template.
// Autogenerated -- Do not edit!
// Generated by extract.py for Jgments:
//   http://s/?fileprint=//depot/google3/third_party/java_src/java/com/google/jgments/extract.py.

package ${package};

import com.google.common.collect.ImmutableMap;

import java.util.Map;

public class Lexers {

  private Lexers() { }

  // TODO(jacobly): avoid paying the penalty of instantiating all lexers
  // for clients that do not need all of them.
  public static final Map<String, LanguageDefinition> ALL
      = new ImmutableMap.Builder<String, LanguageDefinition>()
  % for name, lexer in lexers.items():
          .put("${name}", ${lexer}.INSTANCE)
  % endfor
          .build();

  public static String guessLanguage(String fileName) {
    for (Map.Entry<String, LanguageDefinition> entry : ALL.entrySet()) {
      if (entry.getValue().isApplicable(fileName)) {
        return entry.getKey();
      }
    }
    return null;
  }
}
