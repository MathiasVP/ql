// generated by codegen
/**
 * This module provides the generated definition of `IfExpr`.
 * INTERNAL: Do not import directly.
 */

private import codeql.rust.generated.Synth
private import codeql.rust.generated.Raw
import codeql.rust.elements.Expr

/**
 * INTERNAL: This module contains the fully generated definition of `IfExpr` and should not
 * be referenced directly.
 */
module Generated {
  /**
   * INTERNAL: Do not reference the `Generated::IfExpr` class directly.
   * Use the subclass `IfExpr`, where the following predicates are available.
   */
  class IfExpr extends Synth::TIfExpr, Expr {
    override string getAPrimaryQlClass() { result = "IfExpr" }

    /**
     * Gets the condition of this if expression.
     */
    Expr getCondition() {
      result =
        Synth::convertExprFromRaw(Synth::convertIfExprToRaw(this).(Raw::IfExpr).getCondition())
    }

    /**
     * Gets the then of this if expression.
     */
    Expr getThen() {
      result = Synth::convertExprFromRaw(Synth::convertIfExprToRaw(this).(Raw::IfExpr).getThen())
    }

    /**
     * Gets the else of this if expression, if it exists.
     */
    Expr getElse() {
      result = Synth::convertExprFromRaw(Synth::convertIfExprToRaw(this).(Raw::IfExpr).getElse())
    }

    /**
     * Holds if `getElse()` exists.
     */
    final predicate hasElse() { exists(this.getElse()) }
  }
}
