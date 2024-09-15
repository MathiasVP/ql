// generated by codegen
/**
 * This module provides the generated definition of `OrPat`.
 * INTERNAL: Do not import directly.
 */

private import codeql.rust.generated.Synth
private import codeql.rust.generated.Raw
import codeql.rust.elements.Pat

/**
 * INTERNAL: This module contains the fully generated definition of `OrPat` and should not
 * be referenced directly.
 */
module Generated {
  /**
   * INTERNAL: Do not reference the `Generated::OrPat` class directly.
   * Use the subclass `OrPat`, where the following predicates are available.
   */
  class OrPat extends Synth::TOrPat, Pat {
    override string getAPrimaryQlClass() { result = "OrPat" }

    /**
     * Gets the `index`th argument of this or pat (0-based).
     */
    Pat getArg(int index) {
      result = Synth::convertPatFromRaw(Synth::convertOrPatToRaw(this).(Raw::OrPat).getArg(index))
    }

    /**
     * Gets any of the arguments of this or pat.
     */
    final Pat getAnArg() { result = this.getArg(_) }

    /**
     * Gets the number of arguments of this or pat.
     */
    final int getNumberOfArgs() { result = count(int i | exists(this.getArg(i))) }
  }
}
