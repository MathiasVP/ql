overlay[local?]
module;

/**
 * Provides Java-specific definitions for use in sign analysis.
 */
module Private {
  private import cpp as C
  import semmle.code.cpp.rangeanalysis.new2.RangeUtils as RU
  private import semmle.code.cpp.dataflow.new.DataFlow::DataFlow::Ssa as Ssa
  private import semmle.code.cpp.controlflow.IRGuards as G
  private import SsaReadPositionCommon
  private import Sign
  private import semmle.code.cpp.ir.IR as IR
  import Impl

  class ConstantIntegerExpr = RU::ConstantIntegerExpr;

  class Guard = G::Guards_v1::Guard;

  class SsaVariable extends Ssa::Definition {
    SsaVariable() { this.isCertain() }
  }

  class SsaPhiNode = Ssa::PhiNode;

  class VarAccess extends Expr instanceof IR::LoadInstruction {
    VarAccess() {
      this.getUnconvertedResultExpression().(C::VariableAccess).getTarget() instanceof
        C::StackVariable
    } // TODO: Don't depend on AST here
  }

  class FieldAccess extends Expr instanceof IR::LoadInstruction {
    FieldAccess() { this.getUnconvertedResultExpression() instanceof C::FieldAccess } // TODO: Don't depend on AST here
  }

  class CastingExpr extends IR::ConvertInstruction {
    /** Gets the source type of this cast. */
    C::Type getSourceType() { result = this.getUnary().getResultType() }
  }

  class Type = C::Type;

  class Expr extends IR::Instruction {
    Type getType() { result = this.getResultType() }
  }

  class ComparisonExpr extends Expr instanceof IR::RelationalInstruction {
    Expr getLesserOperand() { result = super.getLesser() }

    Expr getGreaterOperand() { result = super.getGreater() }

    predicate isStrict() { super.isStrict() }
  }

  class VariableUpdate extends Expr instanceof IR::StoreInstruction {
    Expr getSourceValue() { result = super.getSourceValue() }
  }

  class Field = C::Field;

  class DivExpr extends Expr instanceof IR::DivInstruction {
    Expr getLeftOperand() { result = super.getLeft() }

    Expr getRightOperand() { result = super.getRight() }
  }

  /** Class to represent float and double literals. */
  class RealLiteral extends Expr instanceof IR::ConstantInstruction {
    string value;

    RealLiteral() { value = this.getValue() and exists(value.toFloat()) }

    string getValue() { result = super.getValue() }
  }

  class NumericOrCharType extends Type instanceof C::ArithmeticType { }

  /** Class to represent unary operation. */
  class UnaryOperation extends Expr, IR::UnaryInstruction {
    UnaryOperation() {
      this instanceof IR::NegateInstruction
      or
      this instanceof IR::LogicalNotInstruction
    }

    /** Returns the operand of this expression. */
    Expr getOperand() { result = this.getUnary() }

    /** Returns the operation representing this expression. */
    TUnarySignOperation getOp() {
      this instanceof IR::NegateInstruction and result = TNegOp()
      or
      this instanceof IR::LogicalNotInstruction and result = TBitNotOp()
    }
  }

  /** Class to represent binary operation. */
  class BinaryOperation extends Expr, IR::BinaryInstruction {
    BinaryOperation() {
      this instanceof IR::AddInstruction or
      this instanceof IR::SubInstruction or
      this instanceof IR::MulInstruction or
      this instanceof IR::DivInstruction or
      this instanceof IR::RemInstruction or
      this instanceof IR::BitAndInstruction or
      this instanceof IR::BitOrInstruction or
      this instanceof IR::BitXorInstruction or
      this instanceof IR::ShiftLeftInstruction or
      this instanceof IR::ShiftRightInstruction or
      this instanceof IR::UnsignedShiftRightInstruction
    }

    /** Returns the operation representing this expression. */
    TBinarySignOperation getOp() {
      this instanceof IR::AddInstruction and result = TAddOp()
      or
      this instanceof IR::SubInstruction and result = TSubOp()
      or
      this instanceof IR::MulInstruction and result = TMulOp()
      or
      this instanceof IR::DivInstruction and result = TDivOp()
      or
      this instanceof IR::RemInstruction and result = TRemOp()
      or
      this instanceof IR::BitAndInstruction and result = TBitAndOp()
      or
      this instanceof IR::BitOrInstruction and result = TBitOrOp()
      or
      this instanceof IR::BitXorInstruction and result = TBitXorOp()
      or
      this instanceof IR::ShiftLeftInstruction and result = TLeftShiftOp()
      or
      this instanceof IR::ShiftRightInstruction and result = TRightShiftOp()
      or
      this instanceof IR::UnsignedShiftRightInstruction and result = TUnsignedRightShiftOp()
    }

    Expr getLeftOperand() { result = super.getLeft() }

    Expr getRightOperand() { result = super.getRight() }
  }

  predicate ssaRead = RU::ssaRead/2;

  /**
   * Holds if `guard` controls the position `controlled` with the value `testIsTrue`.
   */
  predicate guardControlsSsaRead(Guard guard, SsaReadPosition controlled, boolean testIsTrue) {
    guard.controls(controlled.(SsaReadPositionBlock).getBlock(), testIsTrue)
    or
    exists(SsaReadPositionPhiInputEdge controlledEdge | controlledEdge = controlled |
      guard.controls(controlledEdge.getOrigBlock(), testIsTrue) or
      guard
          .controlsBranchEdge(controlledEdge.getOrigBlock(), controlledEdge.getPhiBlock(),
            testIsTrue)
    )
  }
}

private module Impl {
  private import cpp
  private import semmle.code.cpp.rangeanalysis.new2.RangeUtils
  private import semmle.code.cpp.dataflow.new.DataFlow
  private import DataFlow::Ssa as Ssa
  private import semmle.code.cpp.ir.dataflow.internal.DataFlowPrivate as DataFlowPrivate
  private import semmle.code.cpp.controlflow.IRGuards
  private import Sign
  private import SignAnalysisCommon
  private import SsaReadPositionCommon
  private import semmle.code.cpp.ir.IR as IR
  private import semmle.code.cpp.controlflow.IRGuards

  class UnsignedNumericType = UnsignedCharType;

  class Expr = IR::Instruction;

  class VariableUpdate = Private::VariableUpdate;

  /** Gets the character value of expression `e`. */
  string getCharValue(Expr e) {
    result = e.getUnconvertedResultExpression().(CharLiteral).getValue()
  }

  /** Gets the constant `float` value of non-`ConstantIntegerExpr` expression `e`. */
  float getNonIntegerValue(Expr e) {
    result = e.getUnconvertedResultExpression().getValue().toFloat()
  }

  /**
   * Holds if `e` is an access to the size of a container (`string`, `Map`, or
   * `Collection`).
   */
  predicate containerSizeAccess(Expr e) { none() }

  /** Holds if `e` is by definition strictly positive. */
  predicate positiveExpression(Expr e) { none() }

  /**
   * Holds if `e` has type `NumericOrCharType`, but the sign of `e` is unknown.
   */
  predicate numericExprWithUnknownSign(Expr e) { none() }

  /** Returns the underlying variable update of the explicit SSA variable `v`. */
  Private::VariableUpdate getExplicitSsaAssignment(Ssa::Definition v) {
    result = v.(Ssa::DirectExplicitDefinition).getAssignedInstruction()
  }

  /** Returns the assignment of the variable update `def`. */
  Expr getExprFromSsaAssignment(VariableUpdate def) { result = def.getSourceValue() }

  /** Holds if `def` can have any sign. */
  predicate explicitSsaDefWithAnySign(VariableUpdate def) { none() }

  /** Returns the operand of the operation if `e` is a decrement. */
  Expr getDecrementOperand(Expr e) { none() }

  /** Returns the operand of the operation if `e` is an increment. */
  Expr getIncrementOperand(Expr e) { none() }

  /** Gets the variable underlying the implicit SSA variable `v`. */
  Variable getImplicitSsaDeclaration(Ssa::Definition v) { none() }

  /** Holds if the variable underlying the implicit SSA variable `v` is not a field. */
  predicate nonFieldImplicitSsaDefinition(Ssa::Definition v) { v.isParameterDefinition(_) }

  /** Returned an expression that is assigned to `f`. */
  Expr getAssignedValueToField(Field f) {
    exists(DataFlow::ContentSet cs, DataFlow::FieldContent fc |
      cs.isSingleton(fc) and
      fc.getAField() = f and
      fc.getIndirectionIndex() = 1 and
      DataFlowPrivate::storeStep(DataFlow::instructionNode(result), cs, _)
    )
  }

  /** Holds if `f` can have any sign. */
  predicate fieldWithUnknownSign(Field f) { none() }

  /** Holds if `f` is accessed in an increment operation. */
  predicate fieldIncrementOperationOperand(Field f) { none() }

  /** Holds if `f` is accessed in a decrement operation. */
  predicate fieldDecrementOperationOperand(Field f) { none() }

  /** Returns possible signs of `f` based on the declaration. */
  Sign specificFieldSign(Field f) { anySign(result) and exists(f) }

  /** Returns a sub expression of `e` for expression types where the sign depends on the child. */
  Expr getASubExprWithSameSign(Expr e) {
    result = e.(CopyValueInstruction).getSourceValue()
    or
    result = e.(StoreInstruction).getSourceValue()
    or
    result = e.(ConvertInstruction).getUnary()
  }

  Expr getARead(Ssa::Definition v) { result = v.getAUse().getDef() }

  Field getField(Expr fa) {
    exists(DataFlow::ContentSet cs, DataFlow::FieldContent fc |
      cs.isSingleton(fc) and
      fc.getAField() = result and
      fc.getIndirectionIndex() = 1 and
      DataFlowPrivate::readStep(_, fc, DataFlow::instructionNode(fa))
    )
  }

  Expr getAnExpression(SsaReadPositionBlock bb) { result = bb.getBlock().getAnInstruction() }

  IRGuardCondition getComparisonGuard(IR::RelationalInstruction ce) { result = ce } // TODO: Should this be the branch instruction or the guard?
}
