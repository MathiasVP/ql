// generated by codegen/codegen.py
import codeql.swift.elements.pattern.Pattern

class NamedPatternBase extends @named_pattern, Pattern {
  override string getAPrimaryQlClass() { result = "NamedPattern" }

  string getName() { named_patterns(this, result) }
}
