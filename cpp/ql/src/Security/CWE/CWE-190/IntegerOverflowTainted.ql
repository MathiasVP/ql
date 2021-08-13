/**
 * @name Potential integer arithmetic overflow
 * @description A user-controlled integer arithmetic expression
 *              that is not validated can cause overflows.
 * @kind problem
 * @id cpp/integer-overflow-tainted
 * @problem.severity warning
 * @security-severity 8.1
 * @precision low
 * @tags security
 *       external/cwe/cwe-190
 *       external/cwe/cwe-197
 *       external/cwe/cwe-681
 */

import cpp
import semmle.code.cpp.rangeanalysis.SimpleRangeAnalysis
import semmle.code.cpp.security.TaintTracking

class Config extends Configuration {
  Config() { this = "IntegerOverflowTaintedConfig" }

  override predicate isUnconvertedSink(Expr e) { select0(e, _) }
}

predicate select0(Expr use, Expr origin) {
  not use.getUnspecifiedType() instanceof PointerType and
  tainted(origin, use) and
  origin != use and
  not inSystemMacroExpansion(use) and
  // Avoid double-counting: don't include all the conversions of `use`.
  not use instanceof Conversion
}

/** Holds if `expr` might overflow. */
predicate outOfBoundsExpr(Expr expr, string kind) {
  if convertedExprMightOverflowPositively(expr)
  then kind = "overflow"
  else
    if convertedExprMightOverflowNegatively(expr)
    then kind = "overflow negatively"
    else none()
}

from Expr use, Expr origin, string kind
where
  select0(use, origin) and
  outOfBoundsExpr(use, kind)
select use, "$@ flows to here and is used in an expression which might " + kind + ".", origin,
  "User-provided value"
