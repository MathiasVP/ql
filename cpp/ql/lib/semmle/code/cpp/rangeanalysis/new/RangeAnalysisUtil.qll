/**
 * This file contains the range-analysis specific parts of the `cpp/invalid-pointer-deref`
 * and `cpp/overrun-write` query.
 */

private import cpp
private import semmle.code.cpp.rangeanalysis.new.internal.semantic.analysis.RangeAnalysis
private import semmle.code.cpp.rangeanalysis.new.internal.semantic.SemanticExprSpecific
private import semmle.code.cpp.ir.IR

pragma[nomagic]
private Instruction getABoundIn(SemBound b, IRFunction func) {
  getSemanticExpr(result) = b.getExpr(0) and
  result.getEnclosingIRFunction() = func
}

/**
 * Holds if `i <= b + delta`.
 */
pragma[inline]
private predicate boundedImplCand(Instruction i, Instruction b, float delta) {
  exists(SemBound bound, IRFunction func, float d |
    semBounded(getSemanticExpr(i), bound, d, true, _) and
    b = getABoundIn(bound, func) and
    i.getEnclosingIRFunction() = func and
    delta = normalizeFloatUp(d)
  )
}

/**
 * Holds if `i <= b + delta` and `delta` is the smallest float that satisfies
 * this condition.
 */
pragma[inline]
private predicate boundedImpl(Instruction i, Instruction b, float delta) {
  delta = min(float cand | boundedImplCand(i, b, cand))
}

/**
 * Holds if `i <= b + delta`.
 *
 * This predicate enforces a join-order that ensures that `i` has already been bound.
 */
bindingset[i]
pragma[inline_late]
predicate bounded1(Instruction i, Instruction b, float delta) { boundedImpl(i, b, delta) }

/**
 * Holds if `i <= b + delta`.
 *
 * This predicate enforces a join-order that ensures that `b` has already been bound.
 */
bindingset[b]
pragma[inline_late]
predicate bounded2(Instruction i, Instruction b, float delta) { boundedImpl(i, b, delta) }

/** Holds if `i <= b + delta`. */
predicate bounded = boundedImpl/3;

bindingset[x]
float normalizeFloatUp(float x) { result = x + 0.0 }

bindingset[f1, f2]
predicate le(float f1, float f2) { normalizeFloatUp(f1) <= f2 }

bindingset[f1, f2]
predicate ge(float f1, float f2) { f1 >= normalizeFloatUp(f2) }

bindingset[f1, f2]
predicate lt(float f1, float f2) { normalizeFloatUp(f1) < f2 }

bindingset[f1, f2]
predicate gt(float f1, float f2) { f1 > normalizeFloatUp(f2) }
