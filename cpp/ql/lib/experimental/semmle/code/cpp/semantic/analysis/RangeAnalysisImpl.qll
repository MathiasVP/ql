private import RangeAnalysisStage
private import RangeAnalysisSpecific
private import experimental.semmle.code.cpp.semantic.analysis.FloatDelta
private import RangeUtils
private import experimental.semmle.code.cpp.semantic.SemanticBound as SemanticBound
private import experimental.semmle.code.cpp.semantic.SemanticLocation
private import experimental.semmle.code.cpp.semantic.SemanticSSA

module ConstantBounds implements BoundSig<FloatDelta> {
  class SemBound instanceof SemanticBound::SemBound {
    SemBound() {
      this instanceof SemanticBound::SemZeroBound
      or
      this.(SemanticBound::SemSsaBound).getAVariable() instanceof SemSsaPhiNode
    }

    string toString() { result = super.toString() }

    SemLocation getLocation() { result = super.getLocation() }

    SemExpr getExpr(float delta) { result = super.getExpr(delta) }
  }

  class SemZeroBound extends SemBound instanceof SemanticBound::SemZeroBound { }

  class SemSsaBound extends SemBound instanceof SemanticBound::SemSsaBound {
    SemSsaVariable getAVariable() { result = this.(SemanticBound::SemSsaBound).getAVariable() }
  }
}

private module RelativeBounds implements BoundSig<FloatDelta> {
  class SemBound instanceof SemanticBound::SemBound {
    SemBound() { not this instanceof SemanticBound::SemZeroBound }

    string toString() { result = super.toString() }

    SemLocation getLocation() { result = super.getLocation() }

    SemExpr getExpr(float delta) { result = super.getExpr(delta) }
  }

  class SemZeroBound extends SemBound instanceof SemanticBound::SemZeroBound { }

  class SemSsaBound extends SemBound instanceof SemanticBound::SemSsaBound {
    SemSsaVariable getAVariable() { result = this.(SemanticBound::SemSsaBound).getAVariable() }
  }
}

module WithoutNonlinearRecursion<
  DeltaSig D, BoundSig<D> Bounds, LangSig<D> LangParam, UtilSig<D> UtilParam> implements
  NonlinearRecursionSig<D, Bounds, LangParam, UtilParam>
{
  predicate bounded(
    SemExpr e, Bounds::SemBound b, D::Delta delta, boolean upper, boolean fromBackEdge,
    D::Delta origdelta
  ) {
    none()
  }
}

module WithNonlinearRecursion<
  DeltaSig D, BoundSig<D> Bounds, LangSig<D> LangParam, UtilSig<D> UtilParam> implements
  NonlinearRecursionSig<D, Bounds, LangParam, UtilParam>
{
  private module Self = WithNonlinearRecursion<D, Bounds, LangParam, UtilParam>;

  private module Main = RangeStage<D, Bounds, LangParam, UtilParam, Self>;

  predicate bounded(
    SemExpr e, Bounds::SemBound b, D::Delta delta, boolean upper, boolean fromBackEdge,
    D::Delta origdelta
  ) {
    fromBackEdge = false and
    b instanceof Bounds::SemZeroBound and
    exists(
      SemAddExpr add, SemExpr left, SemExpr right, D::Delta dLeft, D::Delta dRight,
      D::Delta origdeltaLeft, D::Delta origdeltaRight
    |
      // Don't compute non-linear bounds if we can already compute the bounds in the main recursion.
      not Main::boundFlowStep(add, _, _, _) and
      not Main::semValueFlowStep(add, _, _) and
      e = add and
      add.getLeftOperand() = left and
      add.getRightOperand() = right and
      // Requiring that both `fromBackEdge`s are `false` prevents us from entering an ever-increasing
      // sequence of recursive calls that continiously increments (or decrements) the bound.
      Main::bounded(left, any(Bounds::SemZeroBound zb), dLeft, upper, false, origdeltaLeft, _) and
      Main::bounded(right, any(Bounds::SemZeroBound zb), dRight, upper, false, origdeltaRight, _)
    |
      upper = true and
      delta = D::fromFloat(D::toFloat(dLeft) + D::toFloat(dRight)) and
      origdelta = D::fromFloat(D::toFloat(origdeltaLeft) + D::toFloat(origdeltaRight))
      or
      upper = false and
      delta = D::fromFloat(D::toFloat(dLeft) - D::toFloat(dRight)) and
      origdelta = D::fromFloat(D::toFloat(origdeltaLeft) - D::toFloat(origdeltaRight))
    )
  }
}

module Utils = RangeUtil<FloatDelta, CppLangImpl>;

private module ConstantStage =
  RangeStage<FloatDelta, ConstantBounds, CppLangImpl, Utils,
    WithNonlinearRecursion<FloatDelta, ConstantBounds, CppLangImpl, Utils>>;

private module RelativeStage =
  RangeStage<FloatDelta, RelativeBounds, CppLangImpl, Utils,
    WithoutNonlinearRecursion<FloatDelta, RelativeBounds, CppLangImpl, Utils>>;

private newtype TSemReason =
  TSemNoReason() or
  TSemCondReason(SemGuard guard) {
    guard = any(ConstantStage::SemCondReason reason).getCond()
    or
    guard = any(RelativeStage::SemCondReason reason).getCond()
  }

/**
 * A reason for an inferred bound. This can either be `CondReason` if the bound
 * is due to a specific condition, or `NoReason` if the bound is inferred
 * without going through a bounding condition.
 */
abstract class SemReason extends TSemReason {
  /** Gets a textual representation of this reason. */
  abstract string toString();
}

/**
 * A reason for an inferred bound that indicates that the bound is inferred
 * without going through a bounding condition.
 */
class SemNoReason extends SemReason, TSemNoReason {
  override string toString() { result = "NoReason" }
}

/** A reason for an inferred bound pointing to a condition. */
class SemCondReason extends SemReason, TSemCondReason {
  /** Gets the condition that is the reason for the bound. */
  SemGuard getCond() { this = TSemCondReason(result) }

  override string toString() { result = getCond().toString() }
}

private ConstantStage::SemReason constantReason(SemReason reason) {
  result instanceof ConstantStage::SemNoReason and reason instanceof SemNoReason
  or
  result.(ConstantStage::SemCondReason).getCond() = reason.(SemCondReason).getCond()
}

private RelativeStage::SemReason relativeReason(SemReason reason) {
  result instanceof RelativeStage::SemNoReason and reason instanceof SemNoReason
  or
  result.(RelativeStage::SemCondReason).getCond() = reason.(SemCondReason).getCond()
}

predicate semBounded(
  SemExpr e, SemanticBound::SemBound b, float delta, boolean upper, SemReason reason
) {
  ConstantStage::semBounded(e, b, delta, upper, constantReason(reason))
  or
  RelativeStage::semBounded(e, b, delta, upper, relativeReason(reason))
}
