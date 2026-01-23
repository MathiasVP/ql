/**
 * This file contains the range-analysis specific parts of the `cpp/invalid-pointer-deref`
 * and `cpp/overrun-write` query.
 */

private import cpp
private import RangeAnalysis
private import semmle.code.cpp.ir.IR

pragma[nomagic]
private Instruction getABoundIn(Bound b, IRFunction func) {
  result = b.getExpr(0) and
  result.getEnclosingIRFunction() = func
}

/**
 * Holds if `i <= b + delta` (if `upper = true`), or `i >= b + delta` (if `upper = false`).
 */
pragma[inline]
private predicate boundedImplCand(Instruction i, Instruction b, int delta) {
  exists(Bound bound, IRFunction func |
    bounded(i, bound, delta, true, _) and
    b = getABoundIn(bound, func) and
    i.getEnclosingIRFunction() = func
  )
}

/**
 * Holds if `i <= b + delta` (if `upper = true`), or `i >= b + delta` (if `upper = false`),
 * and `delta` is the smallest (if `upper = true`) / largest (if `upper = false`) integer that satisfies this condition.
 */
pragma[inline]
private predicate boundedImpl(Instruction i, Instruction b, int delta) {
  delta = min(int cand | boundedImplCand(i, b, cand))
}

/**
 * Holds if `i <= b + delta`.
 *
 * This predicate enforces a join-order that ensures that `i` has already been bound.
 */
bindingset[i]
pragma[inline_late]
predicate bounded1(Instruction i, Instruction b, int delta) {
  boundedImpl(i, b, delta)
}

/**
 * Holds if `i <= b + delta` (if `upper = true`), or `i >= b + delta` (if `upper = false`).
 *
 * This predicate enforces a join-order that ensures that `b` has already been bound.
 */
bindingset[b]
pragma[inline_late]
predicate bounded2(Instruction i, Instruction b, int delta) {
  boundedImpl(i, b, delta)
}

/**
 * Holds if `i <= b + delta` (if `upper = true`), or `i >= b + delta` (if `upper = false`).
 */
predicate bounded = boundedImpl/3;
