/**
 * Provides classes and predicates for range analysis.
 *
 * An inferred bound can either be a specific integer, the abstract value of an
 * SSA variable, or the abstract value of an interesting expression. The latter
 * category includes array lengths that are not SSA variables.
 *
 * If an inferred bound relies directly on a condition, then this condition is
 * reported as the reason for the bound.
 */
overlay[local?]
module;

/*
 * This library tackles range analysis as a flow problem. Consider e.g.:
 * ```
 *   len = arr.length;
 *   if (x < len) { ... y = x-1; ... y ... }
 * ```
 * In this case we would like to infer `y <= arr.length - 2`, and this is
 * accomplished by tracking the bound through a sequence of steps:
 * ```
 *   arr.length --> len = .. --> x < len --> x-1 --> y = .. --> y
 * ```
 *
 * In its simplest form the step relation `E1 --> E2` relates two expressions
 * such that `E1 <= B` implies `E2 <= B` for any `B` (with a second separate
 * step relation handling lower bounds). Examples of such steps include
 * assignments `E2 = E1` and conditions `x <= E1` where `E2` is a use of `x`
 * guarded by the condition.
 *
 * In order to handle subtractions and additions with constants, and strict
 * comparisons, the step relation is augmented with an integer delta. With this
 * generalization `E1 --(delta)--> E2` relates two expressions and an integer
 * such that `E1 <= B` implies `E2 <= B + delta` for any `B`. This corresponds
 * to the predicate `boundFlowStep`.
 *
 * The complete range analysis is then implemented as the transitive closure of
 * the step relation summing the deltas along the way. If `E1` transitively
 * steps to `E2`, `delta` is the sum of deltas along the path, and `B` is an
 * interesting bound equal to the value of `E1` then `E2 <= B + delta`. This
 * corresponds to the predicate `bounded`.
 *
 * Phi nodes need a little bit of extra handling. Consider `x0 = phi(x1, x2)`.
 * There are essentially two cases:
 * - If `x1 <= B + d1` and `x2 <= B + d2` then `x0 <= B + max(d1,d2)`.
 * - If `x1 <= B + d1` and `x2 <= x0 + d2` with `d2 <= 0` then `x0 <= B + d1`.
 * The first case is for whenever a bound can be proven without taking looping
 * into account. The second case is relevant when `x2` comes from a back-edge
 * where we can prove that the variable has been non-increasing through the
 * loop-iteration as this means that any upper bound that holds prior to the
 * loop also holds for the variable during the loop.
 * This generalizes to a phi node with `n` inputs, so if
 * `x0 = phi(x1, ..., xn)` and `xi <= B + delta` for one of the inputs, then we
 * also have `x0 <= B + delta` if we can prove either:
 * - `xj <= B + d` with `d <= delta` or
 * - `xj <= x0 + d` with `d <= 0`
 * for each input `xj`.
 *
 * As all inferred bounds can be related directly to a path in the source code
 * the only source of non-termination is if successive redundant (and thereby
 * increasingly worse) bounds are calculated along a loop in the source code.
 * We prevent this by weakening the bound to a small finite set of bounds when
 * a path follows a second back-edge (we postpone weakening till the second
 * back-edge as a precise bound might require traversing a loop once).
 */

import cpp as C
private import semmle.code.cpp.dataflow.new.DataFlow::DataFlow
private import semmle.code.cpp.ir.IR as IR
private import RangeUtils
private import SignAnalysis
import Bound
private import codeql.rangeanalysis.RangeAnalysis

module Sem implements Semantic<C::Location> {
  private import semmle.code.cpp.dataflow.new.DataFlow::DataFlow::Ssa as SSA
  private import RangeUtils as RU
  private import semmle.code.cpp.controlflow.IRGuards as G

  class Expr extends IR::Instruction {
    BasicBlock getBasicBlock() { result = this.getBlock() }
  }

  class ConstantIntegerExpr extends Expr, RU::ConstantIntegerExpr { }

  abstract class BinaryExpr extends Expr {
    Expr getLeftOperand() { result = this.(IR::BinaryInstruction).getLeft() }

    Expr getRightOperand() { result = this.(IR::BinaryInstruction).getRight() }

    final Expr getAnOperand() { result = this.getLeftOperand() or result = this.getRightOperand() }

    final predicate hasOperands(Expr e1, Expr e2) {
      this.getLeftOperand() = e1 and this.getRightOperand() = e2
      or
      this.getLeftOperand() = e2 and this.getRightOperand() = e1
    }
  }

  class AddExpr extends BinaryExpr {
    AddExpr() { this instanceof IR::AddInstruction or this instanceof IR::PointerAddInstruction }
  }

  class SubExpr extends BinaryExpr {
    SubExpr() { this instanceof IR::SubInstruction or this instanceof IR::PointerSubInstruction }
  }

  class MulExpr extends BinaryExpr instanceof IR::MulInstruction { }

  class DivExpr extends BinaryExpr instanceof IR::DivInstruction { }

  class RemExpr extends BinaryExpr instanceof IR::RemInstruction { }

  class BitAndExpr extends BinaryExpr instanceof IR::BitAndInstruction { }

  class BitOrExpr extends BinaryExpr instanceof IR::BitOrInstruction { }

  class ShiftLeftExpr extends BinaryExpr instanceof IR::ShiftLeftInstruction { }

  class ShiftRightExpr extends BinaryExpr instanceof IR::ShiftRightInstruction { }

  class ShiftRightUnsignedExpr extends BinaryExpr instanceof IR::UnsignedShiftRightInstruction { }

  predicate isAssignOp(BinaryExpr bin) { bin instanceof IR::StoreInstruction }

  class RelationalExpr extends Expr, IR::RelationalInstruction {
    Expr getLesserOperand() { result = this.getLesser() }

    Expr getGreaterOperand() { result = this.getGreater() }
  }

  abstract class UnaryExpr extends Expr {
    abstract Expr getOperand();
  }

  class ConvertExpr extends UnaryExpr {
    IR::Instruction operand;

    ConvertExpr() {
      this.(IR::ConvertInstruction).getUnary() = operand
      or
      this.(IR::InheritanceConversionInstruction).getUnary() = operand
      or
      this.(IR::CheckedConvertOrNullInstruction).getUnary() = operand
      or
      exists(IR::BuiltInInstruction builtin |
        this = builtin and
        builtin.getBuiltInOperation() instanceof C::BuiltInBitCast and
        builtin.getAnOperand().getDef() = operand
      )
    }

    override Expr getOperand() { result = operand }
  }

  class BoxExpr extends UnaryExpr {
    BoxExpr() { none() }

    override Expr getOperand() { none() }
  }

  class UnboxExpr extends UnaryExpr {
    UnboxExpr() { none() }

    override Expr getOperand() { none() }
  }

  class NegateExpr extends UnaryExpr instanceof IR::NegateInstruction {
    override Expr getOperand() { result = super.getUnary() }
  }

  class PreIncExpr extends UnaryExpr {
    PreIncExpr() { none() }

    override Expr getOperand() { none() }
  }

  class PreDecExpr extends UnaryExpr {
    PreDecExpr() { none() }

    override Expr getOperand() { none() }
  }

  class PostIncExpr extends UnaryExpr {
    PostIncExpr() { none() }

    override Expr getOperand() { none() }
  }

  class PostDecExpr extends UnaryExpr {
    PostDecExpr() { none() }

    override Expr getOperand() { none() }
  }

  class CopyValueExpr extends UnaryExpr instanceof IR::CopyInstruction {
    override Expr getOperand() { result = super.getSourceValue() }
  }

  class ConditionalExpr extends Expr {
    ConditionalExpr() { none() }

    Expr getBranchExpr(boolean branch) { none() }
  }

  class BasicBlock = IR::IRCfg::BasicBlock;

  BasicBlock getABasicBlockSuccessor(BasicBlock bb) { result = bb.getASuccessor() }

  private predicate id(C::Element x, C::Element y) { x = y }

  private predicate idOfAst(C::Element x, int y) = equivalenceRelation(id/2)(x, y)

  private predicate idOf(BasicBlock x, int y) { idOfAst(x.getFirstInstruction().getAst(), y) }

  int getBlockId1(BasicBlock bb) { idOf(bb, result) }

  class Guard extends G::Guards_v1::Guard {
    Expr asExpr() { result = this }

    predicate isEquality(Expr e1, Expr e2, boolean polarity) { super.isEquality(e1, e2, polarity) }
  }

  class Type = C::Type;

  class IntegerType extends Type, C::IntegralOrEnumType {
    int getByteSize() { result = super.getSize() }

    predicate isSigned() {
      this.(C::IntegralType).isSigned()
      or
      // Enumerations are
      exists(C::Enum enum | enum = this |
        enum.getExplicitUnderlyingType().(C::IntegralType).isSigned()
        or
        not enum.getExplicitUnderlyingType() instanceof C::IntegralType and
        enum.getAnEnumConstant().getValue().toInt() < 0
      )
    }
  }

  class FloatingPointType extends Type instanceof C::FloatType { }

  class AddressType extends Type {
    AddressType() {
      this instanceof C::PointerType
      or
      this instanceof C::FunctionPointerIshType
      or
      this instanceof C::ArrayType
    }
  }

  Type getExprType(Expr e) { result = e.getResultType() }

  Type getSsaType(SsaVariable var) { result = var.getSourceVariable().getType() }

  final private class FinalSsaVariable = SSA::Definition;

  class SsaVariable extends FinalSsaVariable {
    SsaVariable() { this.isCertain() }

    Expr getAUse() { result = super.getAUse().getDef() }
  }

  class SsaPhiNode extends SsaVariable instanceof SSA::PhiNode {
    predicate hasInputFromBlock(SsaVariable inp, BasicBlock bb) { super.hasInputFromBlock(inp, bb) }
  }

  class SsaExplicitUpdate extends SsaVariable instanceof SSA::DirectExplicitDefinition {
    Expr getDefiningExpr() { result = super.getAssignedInstruction() }
  }

  predicate additionalValueFlowStep(Expr e2, Expr e1, int delta) {
    RU::additionalValueFlowStep(e2, e1, delta)
  }

  predicate conversionCannotOverflow = safeCast/2;
}

module SignInp implements SignAnalysisSig<C::Location, Sem> {
  private import SignAnalysis
  private import internal.Sign

  predicate semPositive(Sem::Expr e) { positive(e) }

  predicate semNegative(Sem::Expr e) { negative(e) }

  predicate semStrictlyPositive(Sem::Expr e) { strictlyPositive(e) }

  predicate semStrictlyNegative(Sem::Expr e) { strictlyNegative(e) }

  predicate semMayBePositive(Sem::Expr e) { exprSign(e) = TPos() }

  predicate semMayBeNegative(Sem::Expr e) { exprSign(e) = TNeg() }
}

module Modulus implements ModulusAnalysisSig<C::Location, Sem> {
  class ModBound = Bound;

  private import codeql.rangeanalysis.ModulusAnalysis as Mod

  predicate exprModulus(Sem::Expr e, ModBound b, int val, int mod) {
    Mod::ModulusAnalysis<C::Location, Sem, IntDelta, Bounds>::exprModulus(e, b, val, mod)
  }
}

module IntDelta implements DeltaSig {
  class Delta = int;

  bindingset[d]
  bindingset[result]
  float toFloat(Delta d) { result = d }

  bindingset[d]
  bindingset[result]
  int toInt(Delta d) { result = d }

  bindingset[n]
  bindingset[result]
  Delta fromInt(int n) { result = n }

  bindingset[f]
  Delta fromFloat(float f) { result = f }
}

/**
 * Holds if `lb` and `ub` are the lower and upper bounds of the unspecified
 * type `t`.
 *
 * For example, if `t` is a signed 32-bit type then holds if `lb` is
 * `-2^31` and `ub` is `2^31 - 1`.
 */
private predicate typeBounds(C::ArithmeticType t, float lb, float ub) {
  exists(C::IntegralType integralType, float limit |
    integralType = t and limit = 2.pow(8 * integralType.getSize())
  |
    if integralType instanceof C::BoolType
    then lb = 0 and ub = 1
    else
      if integralType.isSigned()
      then (
        lb = -(limit / 2) and ub = (limit / 2) - 1
      ) else (
        lb = 0 and ub = limit - 1
      )
  )
  or
  // This covers all floating point types. The range is (-Inf, +Inf).
  t instanceof C::FloatingPointType and lb = -(1.0 / 0.0) and ub = 1.0 / 0.0
}

module CppLangImpl implements LangSig<C::Location, Sem, IntDelta> {
  /**
   * Holds if `e >= bound` (if `upper = false`) or `e <= bound` (if `upper = true`).
   */
  predicate hasConstantBound(Sem::Expr e, int bound, boolean upper) {
    // exists(IR::ConvertInstruction conv, Sem::IntegerType fromType, Sem::IntegerType toType |
    //   safeCast(fromType, toType) and
    //   conv = e and
    //   fromType = conv.getUnary().getResultType() and
    //   toType = e.getResultType() and
    //   // casting to larger type
    //   fromType.getSize() < toType.getSize() and
    //   upper = true and
    //   typeBounds(toType, bound, _)
    // )
    none()
  }

  /**
   * Holds if `e2 >= e1 + delta` (if `upper = false`) or `e2 <= e1 + delta` (if `upper = true`).
   */
  predicate additionalBoundFlowStep(Sem::Expr e2, Sem::Expr e1, int delta, boolean upper) { none() }

  predicate ignoreExprBound(Sem::Expr e) { none() }
}

module Bounds implements BoundSig<C::Location, Sem, IntDelta> {
  final private class FinalBound = Bound;

  class SemBound extends FinalBound {
    Sem::Expr getExpr(int delta) { result = super.getExpr(delta) }

    Sem::Expr getExpr() { result = this.getExpr(0) }
  }

  class SemZeroBound extends SemBound instanceof ZeroBound { }

  class SemSsaBound extends SemBound instanceof SsaBound {
    Sem::SsaVariable getVariable() { result = super.getSsa() }
  }
}

module Overflow implements OverflowSig<C::Location, Sem, IntDelta> {
  predicate semExprDoesNotOverflow(boolean positively, Sem::Expr expr) {
    positively = [true, false] and exists(expr)
  }
}

module Range =
  RangeStage<C::Location, Sem, IntDelta, Bounds, Overflow, CppLangImpl, SignInp, Modulus>;

predicate bounded = Range::semBounded/5;

class Reason = Range::SemReason;

class NoReason = Range::SemNoReason;

class CondReason = Range::SemCondReason;

/**
 * Holds if a cast from `fromtyp` to `totyp` can be ignored for the purpose of
 * range analysis.
 */
private predicate safeCast(C::Type fromType, C::Type toType) {
  exists(Sem::IntegerType fromTypeInt |
    fromType.getUnspecifiedType() = fromTypeInt and
    fromType.getSize() <= toType.getSize()
  |
    fromTypeInt.isSigned() and
    (
      toType.getUnderlyingType().(Sem::IntegerType).isSigned()
      or
      toType.getUnspecifiedType() instanceof Sem::FloatingPointType
    )
    or
    not fromTypeInt.isSigned() and
    exists(Sem::IntegerType toIntType |
      toIntType = toType.getUnspecifiedType() and
      not toIntType.isSigned()
    )
  )
  or
  fromType.getUnspecifiedType() instanceof Sem::FloatingPointType and
  toType.getUnspecifiedType() instanceof Sem::FloatingPointType and
  fromType.getSize() <= toType.getSize()
  or
  fromType.getUnspecifiedType() instanceof Sem::AddressType and
  toType.getUnspecifiedType() instanceof Sem::AddressType
  or
  fromType.getUnspecifiedType().(Sem::IntegerType).getByteSize() <=
    toType.getUnspecifiedType().(Sem::AddressType).getSize()
  or
  fromType.getUnspecifiedType().(C::ArrayType).getBaseType().getUnspecifiedType() =
    toType.getUnspecifiedType().(C::PointerType).getBaseType().getUnspecifiedType()
}
