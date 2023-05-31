// generated by codegen/codegen.py
private import codeql.swift.generated.Synth
private import codeql.swift.generated.Raw
import codeql.swift.elements.stmt.LabeledConditionalStmt
import codeql.swift.elements.stmt.Stmt

module Generated {
  class IfStmt extends Synth::TIfStmt, LabeledConditionalStmt {
    override string getAPrimaryQlClass() { result = "IfStmt" }

    /**
     * Gets the then of this if statement.
     */
    Stmt getThen() {
      result = Synth::convertStmtFromRaw(Synth::convertIfStmtToRaw(this).(Raw::IfStmt).getThen())
    }

    /**
     * Gets the else of this if statement, if it exists.
     */
    Stmt getElse() {
      result = Synth::convertStmtFromRaw(Synth::convertIfStmtToRaw(this).(Raw::IfStmt).getElse())
    }

    /**
     * Holds if `getElse()` exists.
     */
    final predicate hasElse() { exists(this.getElse()) }
  }
}
