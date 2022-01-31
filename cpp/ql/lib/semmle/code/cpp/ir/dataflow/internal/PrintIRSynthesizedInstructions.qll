private import cpp
// The `ValueNumbering` library has to be imported right after `cpp` to ensure
// that the cached IR gets the same checksum here as it does in queries that use
// `ValueNumbering` without `DataFlow`.
private import semmle.code.cpp.ir.ValueNumbering
private import semmle.code.cpp.ir.IR
private import PrintIRUtilities
private import SsaInternals as Ssa

/**
 * Property provider for synthesized SSA instructions.
 */
class LocalFlowPropertyProvider extends IRPropertyProvider {
  override string getOperandProperty(Operand operand, string key) {
    exists(Ssa::SSAOperand ssaOperand |
      ssaOperand.getOperand() = operand and
      ssaOperand.getSourceVariable().toString() = key and
      result = ssaOperand.getIndex().toString()
    )
  }

  override string getInstructionProperty(Instruction instruction, string key) {
    exists(Ssa::SSAInstruction ssaInstruction |
      ssaInstruction.getInstruction() = instruction and
      ssaInstruction.getSourceVariable().toString() = key and
      result = ssaInstruction.getIndex().toString()
    )
  }
}
