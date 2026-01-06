/**
 * Provides Java-specific definitions for bounds.
 */
overlay[local?]
module;

private import cpp as C
private import semmle.code.cpp.ir.IR as IR
private import semmle.code.cpp.dataflow.new.DataFlow::DataFlow::Ssa as Ssa
private import semmle.code.cpp.rangeanalysis.new2.RangeUtils as RU

class SsaVariable extends Ssa::Definition {
  SsaVariable() { this.isCertain() }
}

class Expr = IR::Instruction;

class Location = C::Location;

class IntegralType = C::IntegralType;

class AddressType extends C::Type {
  AddressType() {
    this instanceof C::PointerType or
    this instanceof C::FunctionPointerIshType or
    this instanceof C::ArrayType
  }
}

class ConstantIntegerExpr = RU::ConstantIntegerExpr;

/** Holds if `e` is a bound expression and it is not an SSA variable read. */
predicate interestingExprBound(Expr e) { none() }
