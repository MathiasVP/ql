/**
 * Provides utility predicates for range analysis.
 */
overlay[local?]
module;

import cpp as C
private import semmle.code.cpp.ir.IR as IR
private import semmle.code.cpp.dataflow.new.DataFlow::DataFlow
private import semmle.code.cpp.controlflow.IRGuards
private import RangeAnalysis
private import codeql.rangeanalysis.internal.RangeUtils

private module U = MakeUtils<C::Location, Sem, IntDelta>;

predicate ssaRead = U::ssaRead/2;

predicate ssaUpdateStep = U::ssaUpdateStep/3;

predicate valueFlowStep = U::valueFlowStep/3;

predicate guardControlsSsaRead = U::guardControlsSsaRead/3;

predicate eqFlowCond = U::eqFlowCond/5;

class Expr = IR::Instruction;

/** An expression that always has the same integer value. */
class ConstantIntegerExpr extends Expr instanceof ConstantInstruction {
  int value;

  ConstantIntegerExpr() {
    this.getValue().toInt() = value and
    this.getResultType() instanceof C::IntegralOrEnumType
  }

  /** Gets the integer value of this expression. */
  int getIntValue() { result = value }
}

/** An expression that always has the same boolean value. */
class ConstantBooleanExpr extends Expr instanceof ConstantInstruction {
  int value;

  ConstantBooleanExpr() {
    this.getResultType() instanceof C::BoolType and
    value = this.getValue().toInt()
  }

  /** Gets the boolean value of this expression. */
  boolean getBooleanValue() { if value = 0 then result = false else result = true }
}

/** An expression that always has the same string value. */
class ConstantStringExpr extends Expr instanceof ConstantInstruction {
  ConstantStringExpr() { none() } // TODO

  /** Get the string value of this expression. */
  string getStringValue() { none() }
}

/**
 * Holds if `e1 + delta` equals `e2`.
 */
predicate additionalValueFlowStep(Expr e2, Expr e1, int delta) { none() }
