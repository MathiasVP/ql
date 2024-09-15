// generated by codegen
/**
 * This module provides the generated definition of `IndexExpr`.
 * INTERNAL: Do not import directly.
 */

private import codeql.rust.generated.Synth
private import codeql.rust.generated.Raw
import codeql.rust.elements.Expr

/**
 * INTERNAL: This module contains the fully generated definition of `IndexExpr` and should not
 * be referenced directly.
 */
module Generated {
  /**
   * INTERNAL: Do not reference the `Generated::IndexExpr` class directly.
   * Use the subclass `IndexExpr`, where the following predicates are available.
   */
  class IndexExpr extends Synth::TIndexExpr, Expr {
    override string getAPrimaryQlClass() { result = "IndexExpr" }

    /**
     * Gets the base of this index expression.
     */
    Expr getBase() {
      result =
        Synth::convertExprFromRaw(Synth::convertIndexExprToRaw(this).(Raw::IndexExpr).getBase())
    }

    /**
     * Gets the index of this index expression.
     */
    Expr getIndex() {
      result =
        Synth::convertExprFromRaw(Synth::convertIndexExprToRaw(this).(Raw::IndexExpr).getIndex())
    }

    /**
     * Holds if this index expression is assignee expression.
     */
    predicate isAssigneeExpr() {
      Synth::convertIndexExprToRaw(this).(Raw::IndexExpr).isAssigneeExpr()
    }
  }
}
