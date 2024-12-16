private import cpp
private import semmle.code.cpp.ir.IR
private import semmle.code.cpp.ir.internal.IRCppLanguage as Lang

class DataFlowExpr = Expr;

final private class TypeFinal = Type;

class DataFlowType extends TypeFinal {
  string toString() { result = "" }
}

bindingset[n]
string repeatStars(int n) { result = concat(int i | i = [1 .. n] | "*") }

class PointerOrArrayOrReferenceType extends DerivedType {
  PointerOrArrayOrReferenceType() {
    this instanceof PointerType
    or
    this instanceof ArrayType
    or
    this instanceof ReferenceType
  }
}

/** A variable that behaves like a global variable. */
class GlobalLikeVariable extends Variable {
  GlobalLikeVariable() {
    this instanceof GlobalOrNamespaceVariable or
    this instanceof StaticLocalVariable
  }
}

/**
 * Holds if `operand` is an operand that is not used by the dataflow library.
 * Ignored operands are not recognized as uses by SSA, and they don't have a
 * corresponding `(Indirect)OperandNode`.
 */
predicate ignoreOperand(Operand operand) {
  operand = any(Instruction instr | ignoreInstruction(instr)).getAnOperand() or
  operand = any(Instruction instr | ignoreInstruction(instr)).getAUse() or
  operand instanceof MemoryOperand
}

/**
 * Holds if `instr` is an instruction that is not used by the dataflow library.
 * Ignored instructions are not recognized as reads/writes by SSA, and they
 * don't have a corresponding `(Indirect)InstructionNode`.
 */
predicate ignoreInstruction(Instruction instr) {
  instr instanceof CallSideEffectInstruction or
  instr instanceof CallReadSideEffectInstruction or
  instr instanceof ExitFunctionInstruction or
  instr instanceof EnterFunctionInstruction or
  instr instanceof WriteSideEffectInstruction or
  instr instanceof PhiInstruction or
  instr instanceof ReadSideEffectInstruction or
  instr instanceof ChiInstruction or
  instr instanceof InitializeIndirectionInstruction or
  instr instanceof AliasedDefinitionInstruction or
  instr instanceof AliasedUseInstruction or
  instr instanceof InitializeNonLocalInstruction or
  instr instanceof ReturnIndirectionInstruction or
  instr instanceof UninitializedGroupInstruction
}

/**
 * Gets the instruction that uses this operand, if the instruction is not
 * ignored for dataflow purposes.
 */
Instruction getUse(Operand op) {
  result = op.getUse() and
  not ignoreInstruction(result)
}

/** Gets a use of the instruction `instr` that is not ignored for dataflow purposes. */
Operand getAUse(Instruction instr) {
  result = instr.getAUse() and
  not ignoreOperand(result)
}

/**
 * Holds if the underlying IR has a suitable instruction to represent a value
 * that would otherwise need to be represented by a dedicated `OperandNode` value.
 *
 * Such operands do not create new `OperandNode` values, but are
 * instead associated with the instruction returned by this predicate.
 */
Instruction getIRRepresentationOfOperand(Operand operand) { operand = unique( | | getAUse(result)) }

/**
 * Gets the C++ type of `this` in the member function `f`.
 * The result is a glvalue if `isGLValue` is true, and
 * a prvalue if `isGLValue` is false.
 */
bindingset[isGLValue]
private Lang::CppType getThisType(MemberFunction f, boolean isGLValue) {
  result.hasType(f.getTypeOfThis(), isGLValue)
}

/**
 * Gets the C++ type of the instruction `i`.
 *
 * This is equivalent to `i.getResultLanguageType()` with the exception
 * of instructions that directly references a `this` IRVariable. In this
 * case, `i.getResultLanguageType()` gives an unknown type, whereas the
 * predicate gives the expected type (i.e., a potentially cv-qualified
 * type `A*` where `A` is the declaring type of the member function that
 * contains `i`).
 */
cached
Lang::CppType getResultLanguageType(Instruction i) {
  if i.(VariableAddressInstruction).getIRVariable() instanceof IRThisVariable
  then
    if i.isGLValue()
    then result = getThisType(i.getEnclosingFunction(), true)
    else result = getThisType(i.getEnclosingFunction(), false)
  else result = i.getResultLanguageType()
}

/**
 * Gets the C++ type of the operand `operand`.
 * This is equivalent to the type of the operand's defining instruction.
 *
 * See `getResultLanguageType` for a description of this behavior.
 */
Lang::CppType getLanguageType(Operand operand) { result = getResultLanguageType(operand.getDef()) }

/**
 * Gets the type of the operand `op`.
 *
 * The boolean `isGLValue` is true if the operand represents a glvalue. In that case,
 * the returned type should be thought of as a pointer type whose base type is given
 * by this predicate.
 */
DataFlowType getOperandType(Operand op, boolean isGLValue) {
  getLanguageType(op).hasType(result, isGLValue)
}

/**
 * Gets the type of the instruction `instr`.
 *
 * The boolean `isGLValue` is true if the operand represents a glvalue. In that case,
 * the returned type should be thought of as a pointer type whose base type is given
 * by this predicate.
 */
DataFlowType getInstructionType(Instruction instr, boolean isGLValue) {
  getResultLanguageType(instr).hasType(result, isGLValue)
}

/**
 * Returns the smallest indirection for the type `t`.
 *
 * For most types this is `1`, but for `ArrayType`s (which are allocated on
 * the stack) this is `0`
 */
int getMinIndirectionsForType(Type t) {
  if t.getUnspecifiedType() instanceof ArrayType then result = 0 else result = 1
}

/**
 * An operand that is defined by a `FieldAddressInstruction`.
 */
class FieldAddress extends Operand {
  FieldAddressInstruction fai;

  FieldAddress() { fai = this.getDef() and not ignoreOperand(this) }

  /** Gets the field associated with this instruction. */
  Field getField() { result = fai.getField() }

  /** Gets the instruction whose result provides the address of the object containing the field. */
  Instruction getObjectAddress() { result = fai.getObjectAddress() }

  /** Gets the operand that provides the address of the object containing the field. */
  Operand getObjectAddressOperand() { result = fai.getObjectAddressOperand() }
}
