private import cpp
import semmle.code.cpp.ir.implementation.raw.IR
private import semmle.code.cpp.ir.implementation.internal.TInstruction
private import TranslatedElement
private import InstructionTag
private import Completion
private import EdgeKind
private import semmle.code.cpp.ir.implementation.raw.internal.IRConstruction
private import semmle.code.cpp.ir.internal.CppType
private import semmle.code.cpp.ir.implementation.raw.internal.TranslatedCondition

predicate isPointer(IRVariable v) { v.getIRType() instanceof IRAddressType }

predicate isBoolean(IRVariable v) { v.getIRType() instanceof IRBooleanType }

predicate isInteger(IRVariable v) {
  v.getIRType() instanceof IRSignedIntegerType
  or
  v.getIRType() instanceof IRUnsignedIntegerType
}

newtype TSplitKindBase =
  TConditionSplitKind(IRVariable v) {
    isPointer(v)
    or
    isBoolean(v)
    or
    isInteger(v)
  }

class SplitKindBase extends TSplitKindBase {
  /** Gets a textual representation of this split. */
  string toString() { none() }
}

newtype TSplit = TConditionSplit(TConditionSplitKind kind, ConditionCompletion c)

class Split extends TSplit {
  /** Gets a textual representation of this split. */
  string toString() { none() }
}

module ConditionSplit {
  private predicate id(@element x, @element y) { x = y }

  private predicate idOf(@element x, int y) = equivalenceRelation(id/2)(x, y)

  private predicate branchStep(
    TranslatedCondition tc, StageInstruction pred, StageInstruction succ, ConditionSplitKind kind,
    ConditionCompletion c
  ) {
    exists(TranslatedValueCondition tvc, Expr e, EdgeKind edge |
      tc = tvc and
      pred = tvc.getInstruction(ValueConditionConditionalBranchTag()) and
      succ = tvc.getInstructionSuccessor(ValueConditionConditionalBranchTag(), _, c) and
      tvc.getExpr().getUnconverted() = e and
      conditionSplitEntry(e, kind.getIRVariable(), edge, c)
    )
    or
    exists(TranslatedLogicalAndExpr tlae |
      tc = tlae and
      branchStep(tlae.getLeftOperand(), pred, succ, kind, c) and
      c.getBranch() = false
    )
    or
    exists(TranslatedLogicalOrExpr tloe |
      tc = tloe and
      branchStep(tloe.getLeftOperand(), pred, succ, kind, c) and
      c.getBranch() = true
    )
  }

  class ConditionSplitKind extends SplitKind, TConditionSplitKind {
    override string toString() { result = this.getListOrder().toString() }

    override int getListOrder() { idOf(this.getIRVariable().getAst(), result) }

    IRVariable getIRVariable() { this = TConditionSplitKind(result) }

    predicate isPointer() { isPointer(this.getIRVariable()) }

    predicate isBoolean() { isBoolean(this.getIRVariable()) }

    predicate isInteger() { isInteger(this.getIRVariable()) }
  }

  int getNextListOrder() { result = 1 }

  EdgeKind fromBoolean(boolean b) {
    b = true and
    result instanceof TrueEdge
    or
    b = false and
    result instanceof FalseEdge
  }

  EdgeKind edgeNot(EdgeKind edge) {
    edge instanceof FalseEdge and
    result instanceof TrueEdge
    or
    edge instanceof TrueEdge and
    result instanceof FalseEdge
  }

  private predicate conditionSplitEntry(Expr e, IRVariable v, EdgeKind edge, ConditionCompletion c) {
    e.(VariableAccess).getTarget() = v.getAst() and edge = fromBoolean(c.getBranch())
    or
    conditionSplitEntry(e.(NotExpr).getOperand(), v, edgeNot(edge), c)
    or
    conditionSplitEntry(e.(LogicalOrExpr).getAnOperand(), v, edge, c) and edge instanceof TrueEdge
    or
    conditionSplitEntry(e.(LogicalAndExpr).getAnOperand(), v, edge, c) and edge instanceof FalseEdge
  }

  private class ConditionSplit extends SplitImpl, TConditionSplit {
    ConditionSplitKind kind;
    ConditionCompletion completion;

    ConditionSplit() { this = TConditionSplit(kind, completion) }

    override ConditionSplitKind getKind() { result = kind }

    ConditionCompletion getCompletion() { result = completion }

    override string toString() {
      result = this.getKind().toString() + ": " + this.getCompletion().toString()
    }

    override predicate hasEntry(StageInstruction pred, StageInstruction succ, Completion c) {
      branchStep(_, pred, succ, this.getKind(), c) and
      c = this.getCompletion()
    }

    override predicate hasEntryScope(Declaration scope, StageInstruction first) { none() }

    override predicate hasExit(StageInstruction pred, StageInstruction succ, Completion c) {
      none()
    }

    override predicate hasExitScope(Declaration scope, StageInstruction last, Completion c) {
      none()
    }

    override predicate hasSuccessor(
      StageInstruction pred, StageInstruction succ, EdgeKind edge, Completion c
    ) {
      not branchStep(_, pred, succ, this.getKind(), _) and
      succ = getInstructionSuccessor(pred, edge, c)
      or
      branchStep(_, pred, succ, this.getKind(), c) and
      c = this.getCompletion()
    }
  }
}

int maxSplits() { result = 5 }

/**
 * Holds if split kinds `sk1` and `sk2` may overlap. That is, they may apply
 * to at least one common AST node inside `scope`.
 */
private predicate overlapping(Declaration scope, SplitKind sk1, SplitKind sk2) {
  exists(StageInstruction e |
    sk1.appliesTo(e) and
    sk2.appliesTo(e) and
    scope = e.getEnclosingFunction()
  )
}

/**
 * A split kind. Each control flow node can have at most one split of a
 * given kind.
 */
abstract class SplitKind instanceof SplitKindBase {
  /** Gets a split of this kind. */
  SplitImpl getASplit() { result.getKind() = this }

  /** Holds if some split of this kind applies to AST node `n`. */
  predicate appliesTo(StageInstruction n) { this.getASplit().appliesTo(n) }

  /**
   * Gets a unique integer representing this split kind. The integer is used
   * to represent sets of splits as ordered lists.
   */
  abstract int getListOrder();

  /** Gets the rank of this split kind among all overlapping kinds for `c`. */
  private int getRank(Declaration scope) {
    this = rank[result](SplitKind sk | overlapping(scope, this, sk) | sk order by sk.getListOrder())
  }

  /**
   * Holds if this split kind is enabled for AST node `n`. For performance reasons,
   * the number of splits is restricted by the `maxSplits()` predicate.
   */
  predicate isEnabled(StageInstruction n) {
    this.appliesTo(n) and
    this.getRank(n.getEnclosingFunction()) <= maxSplits()
  }

  /**
   * Gets the rank of this split kind among all the split kinds that apply to
   * AST node `n`. The rank is based on the order defined by `getListOrder()`.
   */
  int getListRank(StageInstruction n) {
    this.isEnabled(n) and
    this = rank[result](SplitKind sk | sk.appliesTo(n) | sk order by sk.getListOrder())
  }

  /** Gets a textual representation of this split kind. */
  abstract string toString();
}

/** An interface for implementing an entity to split on. */
abstract class SplitImpl extends Split {
  /** Gets the kind of this split. */
  abstract SplitKind getKind();

  /**
   * Holds if this split is entered when control passes from `pred` to `succ` with
   * completion `c`.
   *
   * Invariant: `hasEntry(pred, succ, c) implies succ(pred, succ, c)`.
   */
  abstract predicate hasEntry(StageInstruction pred, StageInstruction succ, Completion c);

  /**
   * Holds if this split is entered when control passes from `scope` to the entry point
   * `first`.
   *
   * Invariant: `hasEntryScope(scope, first) implies scopeFirst(scope, first)`.
   */
  abstract predicate hasEntryScope(Declaration scope, StageInstruction first);

  /**
   * Holds if this split is left when control passes from `pred` to `succ` with
   * completion `c`.
   *
   * Invariant: `hasExit(pred, succ, c) implies succ(pred, succ, c)`.
   */
  abstract predicate hasExit(StageInstruction pred, StageInstruction succ, Completion c);

  /**
   * Holds if this split is left when control passes from `last` out of the enclosing
   * scope `scope` with completion `c`.
   *
   * Invariant: `hasExitScope(scope, last, c) implies scopeLast(scope, last, c)`
   */
  abstract predicate hasExitScope(Declaration scope, StageInstruction last, Completion c);

  /**
   * Holds if this split is maintained when control passes from `pred` to `succ` with
   * completion `c`.
   *
   * Invariant: `hasSuccessor(pred, succ, c) implies succ(pred, succ, c)`
   */
  abstract predicate hasSuccessor(
    StageInstruction pred, StageInstruction succ, EdgeKind edge, Completion c
  );

  /** Holds if this split applies to AST node `n`. */
  final predicate appliesTo(StageInstruction n) {
    this.hasEntry(_, n, _)
    or
    this.hasEntryScope(_, n)
    or
    exists(StageInstruction pred | this.appliesTo(pred) | this.hasSuccessor(pred, n, _, _))
  }

  /**
   * Holds if `succ` is a control flow successor for `pred`, given that `pred`
   * finishes with completion `c`, and this split applies to `pred`.
   */
  pragma[noinline]
  final StageInstruction appliesSucc(StageInstruction pred, EdgeKind kind, Completion c) {
    this.appliesTo(pred) and
    result = getInstructionSuccessor(pred, kind, c)
  }
}

EdgeKind getAMatchingSuccessorType(Completion c) {
  isNormalCompletion(c) and
  result instanceof GotoEdge
  or
  isExceptionCompletion(c) and
  result instanceof ExceptionEdge
  or
  isConditionCompletion(c, true) and
  result instanceof TrueEdge
  or
  isConditionCompletion(c, false) and
  result instanceof FalseEdge
}

predicate scopeFirst(Declaration scope, StageInstruction first) {
  exists(TranslatedRootElement root |
    root.getFunction() = scope and
    first = root.getFirstInstruction()
  )
}

predicate scopeLast(Declaration scope, StageInstruction last, Completion c) {
  exists(TranslatedRootElement root, InstructionTag tag |
    root.last(tag, c) and
    root.getInstruction(tag) = last and
    scope = root.getFunction()
  )
}

private module Reachability {
  /**
   * Holds if `n` is an AST node where the set of possible splits may
   * be different from the set of possible splits for one of `n`'s predecessors.
   * That is, `n` starts a new block of elements with the same set of splits.
   */
  private predicate startsSplits(StageInstruction n) {
    scopeFirst(_, n)
    or
    exists(SplitImpl s |
      s.hasEntry(_, n, _)
      or
      s.hasExit(_, n, _)
    )
    or
    exists(StageInstruction pred, SplitImpl split, Completion c, EdgeKind edge |
      n = getInstructionSuccessor(pred, edge, c)
    |
      split.appliesTo(pred) and
      not split.hasSuccessor(pred, n, edge, c)
    )
  }

  private predicate intraSplitsSucc(StageInstruction pred, StageInstruction succ) {
    succ = getInstructionSuccessor(pred, _, _) and
    not startsSplits(succ)
  }

  private predicate splitsBlockContains(StageInstruction start, StageInstruction n) =
    fastTC(intraSplitsSucc/2)(start, n)

  /**
   * A block of control flow elements where the set of splits is guaranteed
   * to remain unchanged, represented by the first element in the block.
   */
  class SameSplitsBlock extends StageInstruction {
    SameSplitsBlock() { startsSplits(this) }

    /** Gets a control flow element in this block. */
    StageInstruction getAnElement() {
      splitsBlockContains(this, result)
      or
      result = this
    }

    pragma[noinline]
    private SameSplitsBlock getASuccessor(Splits predSplits, Splits succSplits) {
      exists(StageInstruction pred | pred = this.getAnElement() |
        SuccSplits::succSplits(pred, predSplits, result, succSplits, _, _, _)
      )
    }

    /**
     * Holds if the elements of this block are reachable from a callable entry
     *  point, with the splits `splits`.
     */
    predicate isReachable(Declaration scope, Splits splits) {
      // Base case
      succEntrySplits(scope, this, splits, _)
      or
      // Recursive case
      exists(SameSplitsBlock pred, Splits predSplits | pred.isReachable(scope, predSplits) |
        this = pred.getASuccessor(predSplits, splits)
      )
    }
  }
}

/**
 * Provides a predicate for the successor relation with split information,
 * as well as logic used to construct the type `TSplits` representing sets
 * of splits. Only sets of splits that can be reached are constructed, hence
 * the predicates are mutually recursive.
 *
 * For the successor relation
 *
 * ```ql
 * succSplits(StageInstruction pred, Splits predSplits, StageInstruction succ, Splits succSplits, Completion c)
 * ```
 *
 * the following invariants are maintained:
 *
 * 1. `pred` is reachable with split set `predSplits`.
 * 2. For all `split` in `predSplits`:
 *    - If `split.hasSuccessor(pred, succ, c)` then `split` in `succSplits`.
 * 3. For all `split` in `predSplits`:
 *    - If `split.hasExit(pred, succ, c)` and not `split.hasEntry(pred, succ, c)` then
 *      `split` not in `succSplits`.
 * 4. For all `split` with kind not in `predSplits`:
 *    - If `split.hasEntry(pred, succ, c)` then `split` in `succSplits`.
 * 5. For all `split` in `succSplits`:
 *    - `split.hasSuccessor(pred, succ, c)` and `split` in `predSplits`, or
 *    - `split.hasEntry(pred, succ, c)`.
 *
 * The algorithm divides into four cases:
 *
 * 1. The set of splits for the successor is the same as the set of splits
 *    for the predecessor:
 *    a) The successor is in the same `SameSplitsBlock` as the predecessor.
 *    b) The successor is *not* in the same `SameSplitsBlock` as the predecessor.
 * 2. The set of splits for the successor is different from the set of splits
 *    for the predecessor:
 *    a) The set of splits for the successor is *maybe* non-empty.
 *    b) The set of splits for the successor is *always* empty.
 *
 * Only case 2a may introduce new sets of splits, so only predicates from
 * this case are used in the definition of `TSplits`.
 *
 * The predicates in this module are named after the cases above.
 */
private module SuccSplits {
  private predicate succInvariant1(
    Reachability::SameSplitsBlock b, StageInstruction pred, Splits predSplits,
    StageInstruction succ, EdgeKind edge, Completion c
  ) {
    pred = b.getAnElement() and
    b.isReachable(_, predSplits) and
    succ = getInstructionSuccessor(pred, edge, c)
  }

  private predicate case1b0(
    StageInstruction pred, Splits predSplits, StageInstruction succ, EdgeKind edge, Completion c
  ) {
    exists(Reachability::SameSplitsBlock b |
      // Invariant 1
      succInvariant1(b, pred, predSplits, succ, edge, c)
    |
      (succ = b.getAnElement() implies succ = b) and
      // Invariant 4
      not exists(SplitImpl split | split.hasEntry(pred, succ, c))
    )
  }

  /**
   * Case 1b.
   *
   * Invariants 1 and 4 hold in the base case, and invariants 2, 3, and 5 are
   * maintained for all splits in `predSplits` (= `succSplits`), except
   * possibly for the splits in `except`.
   *
   * The predicate is written using explicit recursion, as opposed to a `forall`,
   * to avoid negative recursion.
   */
  private predicate case1bForall(
    StageInstruction pred, Splits predSplits, StageInstruction succ, EdgeKind edge, Completion c,
    Splits except
  ) {
    case1b0(pred, predSplits, succ, edge, c) and
    except = predSplits
    or
    exists(SplitImpl split |
      case1bForallCons(pred, predSplits, succ, edge, c, split, except) and
      split.hasSuccessor(pred, succ, edge, c)
    )
  }

  pragma[noinline]
  private predicate case1bForallCons(
    StageInstruction pred, Splits predSplits, StageInstruction succ, EdgeKind edge, Completion c,
    SplitImpl exceptHead, Splits exceptTail
  ) {
    case1bForall(pred, predSplits, succ, edge, c, TSplitsCons(exceptHead, exceptTail))
  }

  private predicate case1(
    StageInstruction pred, Splits predSplits, StageInstruction succ, EdgeKind edge, Completion c
  ) {
    // Case 1a
    exists(Reachability::SameSplitsBlock b | succInvariant1(b, pred, predSplits, succ, edge, c) |
      succ = b.getAnElement() and
      not succ = b
    )
    or
    // Case 1b
    case1bForall(pred, predSplits, succ, edge, c, TSplitsNil())
  }

  pragma[noinline]
  private SplitImpl succInvariant1GetASplit(
    Reachability::SameSplitsBlock b, StageInstruction pred, Splits predSplits,
    StageInstruction succ, EdgeKind edge, Completion c
  ) {
    succInvariant1(b, pred, predSplits, succ, edge, c) and
    result = predSplits.getASplit()
  }

  private predicate case2aux(
    StageInstruction pred, Splits predSplits, StageInstruction succ, EdgeKind edge, Completion c,
    string debug
  ) {
    exists(Reachability::SameSplitsBlock b |
      succInvariant1(b, pred, predSplits, succ, edge, c) and
      (succ = b.getAnElement() implies succ = b)
    |
      succInvariant1GetASplit(b, pred, predSplits, succ, edge, c).hasExit(pred, succ, c) and
      debug = "1"
      or
      any(SplitImpl split).hasEntry(pred, succ, c) and debug = "2"
    )
  }

  /**
   * Holds if `succSplits` should not inherit a split of kind `sk` from
   * `predSplits`, except possibly because of a split in `except`.
   *
   * The predicate is written using explicit recursion, as opposed to a `forall`,
   * to avoid negative recursion.
   */
  private predicate case2aNoneInheritedOfKindForall(
    StageInstruction pred, Splits predSplits, StageInstruction succ, EdgeKind edge, Completion c,
    SplitKind sk, Splits except, string debug
  ) {
    case2aux(pred, predSplits, succ, edge, c, debug) and
    sk.appliesTo(succ) and
    except = predSplits
    or
    exists(Splits mid, SplitImpl split |
      case2aNoneInheritedOfKindForall(pred, predSplits, succ, edge, c, sk, mid, debug) and
      mid = TSplitsCons(split, except)
    |
      split.getKind() = any(SplitKind sk0 | sk0 != sk and sk0.appliesTo(succ))
      or
      split.hasExit(pred, succ, c)
    )
  }

  pragma[nomagic]
  private predicate entryOfKind(
    StageInstruction pred, StageInstruction succ, Completion c, SplitImpl split, SplitKind sk
  ) {
    split.hasEntry(pred, succ, c) and
    sk = split.getKind()
  }

  /** Holds if `succSplits` should not have a split of kind `sk`. */
  pragma[nomagic]
  private predicate case2aNoneOfKind(
    StageInstruction pred, Splits predSplits, StageInstruction succ, EdgeKind edge, Completion c,
    SplitKind sk, string debug
  ) {
    // None inherited from predecessor
    case2aNoneInheritedOfKindForall(pred, predSplits, succ, edge, c, sk, TSplitsNil(), debug) and
    // None newly entered into
    not entryOfKind(pred, succ, c, _, sk)
  }

  /** Holds if `succSplits` should not have a split of kind `sk` at rank `rnk`. */
  pragma[nomagic]
  private predicate case2aNoneAtRank(
    StageInstruction pred, Splits predSplits, StageInstruction succ, EdgeKind edge, Completion c,
    int rnk, string debug
  ) {
    exists(SplitKind sk | case2aNoneOfKind(pred, predSplits, succ, edge, c, sk, debug) |
      rnk = sk.getListRank(succ)
    )
  }

  pragma[nomagic]
  private SplitImpl case2auxGetAPredecessorSplit(
    StageInstruction pred, Splits predSplits, StageInstruction succ, EdgeKind edge, Completion c,
    string debug
  ) {
    case2aux(pred, predSplits, succ, edge, c, debug) and
    result = predSplits.getASplit()
  }

  /** Gets a split that should be in `succSplits`. */
  pragma[nomagic]
  private SplitImpl case2aSome(
    StageInstruction pred, Splits predSplits, StageInstruction succ, EdgeKind edge, Completion c,
    SplitKind sk, string debug
  ) {
    (
      // Inherited from predecessor
      result = case2auxGetAPredecessorSplit(pred, predSplits, succ, edge, c, debug) and
      result.hasSuccessor(pred, succ, edge, c)
      or
      // Newly entered into
      exists(SplitKind sk0 |
        case2aNoneInheritedOfKindForall(pred, predSplits, succ, edge, c, sk0, TSplitsNil(), debug)
      |
        entryOfKind(pred, succ, c, result, sk0)
      )
    ) and
    sk = result.getKind()
  }

  /** Gets a split that should be in `succSplits` at rank `rnk`. */
  pragma[nomagic]
  SplitImpl case2aSomeAtRank(
    StageInstruction pred, Splits predSplits, StageInstruction succ, EdgeKind edge, Completion c,
    int rnk, string debug
  ) {
    exists(SplitKind sk | result = case2aSome(pred, predSplits, succ, edge, c, sk, debug) |
      rnk = sk.getListRank(succ)
    )
  }

  /**
   * Case 2a.
   *
   * As opposed to the other cases, in this case we need to construct a new set
   * of splits `succSplits`. Since this involves constructing the very IPA type,
   * we cannot recurse directly over the structure of `succSplits`. Instead, we
   * recurse over the ranks of all splits that *might* be in `succSplits`.
   *
   * - Invariant 1 holds in the base case,
   * - invariant 2 holds for all splits with rank at least `rnk`,
   * - invariant 3 holds for all splits in `predSplits`,
   * - invariant 4 holds for all splits in `succSplits` with rank at least `rnk`,
   *   and
   * - invariant 4 holds for all splits in `succSplits` with rank at least `rnk`.
   */
  predicate case2aFromRank(
    StageInstruction pred, Splits predSplits, StageInstruction succ, Splits succSplits,
    EdgeKind edge, Completion c, int rnk, string debug
  ) {
    case2aux(pred, predSplits, succ, edge, c, append("case2aux: ", debug)) and
    succSplits = TSplitsNil() and
    rnk = max(any(SplitKind sk).getListRank(succ)) + 1
    or
    exists(string debug1, string debug2 |
      case2aFromRank(pred, predSplits, succ, succSplits, edge, c, rnk + 1, debug1) and
      case2aNoneAtRank(pred, predSplits, succ, edge, c, rnk, debug2) and
      debug = debug1 + ", " + debug2
    )
    or
    exists(Splits mid, SplitImpl split |
      split = case2aCons(pred, predSplits, succ, mid, edge, c, rnk, debug) and
      succSplits = TSplitsCons(split, mid)
    )
  }

  pragma[noinline]
  private SplitImpl case2aCons(
    StageInstruction pred, Splits predSplits, StageInstruction succ, Splits succSplits,
    EdgeKind edge, Completion c, int rnk, string debug
  ) {
    exists(string debug1, string debug2 |
      debug = debug1 + ", " + debug2 and
      case2aFromRank(pred, predSplits, succ, succSplits, edge, c, rnk + 1, debug1) and
      result = case2aSomeAtRank(pred, predSplits, succ, edge, c, rnk, debug2)
    )
  }

  /**
   * Case 2b.
   *
   * Invariants 1, 4, and 5 hold in the base case, and invariants 2 and 3 are
   * maintained for all splits in `predSplits`, except possibly for the splits
   * in `except`.
   *
   * The predicate is written using explicit recursion, as opposed to a `forall`,
   * to avoid negative recursion.
   */
  private predicate case2bForall(
    StageInstruction pred, Splits predSplits, StageInstruction succ, EdgeKind edge, Completion c,
    Splits except, string debug
  ) {
    // Invariant 1
    case2aux(pred, predSplits, succ, edge, c, debug) and
    // Invariants 4 and 5
    not any(SplitKind sk).appliesTo(succ) and
    except = predSplits
    or
    exists(SplitImpl split |
      case2bForallCons(pred, predSplits, succ, edge, c, split, except, debug)
    |
      // Invariants 2 and 3
      split.hasExit(pred, succ, c)
    )
  }

  pragma[noinline]
  private predicate case2bForallCons(
    StageInstruction pred, Splits predSplits, StageInstruction succ, EdgeKind edge, Completion c,
    SplitImpl exceptHead, Splits exceptTail, string debug
  ) {
    case2bForall(pred, predSplits, succ, edge, c, TSplitsCons(exceptHead, exceptTail), debug)
  }

  bindingset[s1, result]
  string append(string s1, string s2) { s2 = s1 + result }

  private predicate case2(
    StageInstruction pred, Splits predSplits, StageInstruction succ, Splits succSplits,
    EdgeKind edge, Completion c, string debug
  ) {
    case2aFromRank(pred, predSplits, succ, succSplits, edge, c, 1, append("case2aFromRank: ", debug))
    or
    case2bForall(pred, predSplits, succ, edge, c, TSplitsNil(), append("case2bForall: ", debug)) and
    succSplits = TSplitsNil()
  }

  /**
   * Holds if `succ` with splits `succSplits` is a successor of type `t` for `pred`
   * with splits `predSplits`.
   */
  predicate succSplits(
    StageInstruction pred, Splits predSplits, StageInstruction succ, Splits succSplits,
    EdgeKind edge, Completion c, string debug
  ) {
    case1(pred, predSplits, succ, edge, c) and
    succSplits = predSplits and
    debug = ""
    or
    case2(pred, predSplits, succ, succSplits, edge, c, debug)
  }
}

private predicate succEntrySplitsFromRank(
  Declaration pred, StageInstruction succ, Splits splits, int rnk
) {
  splits = TSplitsNil() and
  scopeFirst(pred, succ) and
  rnk = 0
  or
  exists(SplitImpl head, Splits tail | succEntrySplitsCons(pred, succ, head, tail, rnk) |
    splits = TSplitsCons(head, tail)
  )
}

private predicate succEntrySplitsCons(
  Declaration pred, StageInstruction succ, SplitImpl head, Splits tail, int rnk
) {
  succEntrySplitsFromRank(pred, succ, tail, rnk - 1) and
  head.hasEntryScope(pred, succ) and
  rnk = head.getKind().getListRank(succ)
}

/**
 * Holds if `succ` with splits `succSplits` is the first element that is executed
 * when entering callable `pred`.
 */
pragma[noinline]
private predicate succEntrySplits(
  Declaration pred, StageInstruction succ, Splits succSplits, EdgeKind t
) {
  exists(int rnk |
    scopeFirst(pred, succ) and
    isSimple(t) and
    succEntrySplitsFromRank(pred, succ, succSplits, rnk)
  |
    rnk = 0 and
    not any(SplitImpl split).hasEntryScope(pred, succ)
    or
    rnk = max(SplitImpl split | split.hasEntryScope(pred, succ) | split.getKind().getListRank(succ))
  )
}

cached
newtype TSplits =
  TSplitsNil() or
  TSplitsCons(SplitImpl head, Splits tail) {
    exists(
      StageInstruction pred, Splits predSplits, StageInstruction succ, EdgeKind edge, Completion c,
      int rnk
    |
      SuccSplits::case2aFromRank(pred, predSplits, succ, tail, edge, c, rnk + 1, _) and
      head = SuccSplits::case2aSomeAtRank(pred, predSplits, succ, edge, c, rnk, _)
    )
    or
    succEntrySplitsCons(_, _, head, tail, _)
  }

private string getSplitStringAt(Splits split, int index) {
  exists(SplitImpl head, Splits tail | split = TSplitsCons(head, tail) |
    index = 0 and result = head.toString() and result != ""
    or
    index > 0 and result = getSplitStringAt(tail, index - 1)
  )
}

private string getSplitsStringPart(Splits splits, int index) {
  isFullyConstructedSplits(splits) and
  result = getSplitStringAt(splits, index)
}

cached
string splitsToString(Splits splits) {
  result =
    concat(string child, int index |
      child = getSplitsStringPart(splits, index)
    |
      child, ", " order by index
    )
}

/**
 * Holds if `pred` with splits `predSplits` can exit the enclosing callable
 * `succ` with type `t`.
 */
private predicate succExitSplits(
  StageInstruction pred, Splits predSplits, Declaration succ, EdgeKind t
) {
  exists(Reachability::SameSplitsBlock b, Completion c | pred = b.getAnElement() |
    b.isReachable(succ, predSplits) and
    t = getAMatchingSuccessorType(c) and
    scopeLast(succ, pred, c) and
    forall(SplitImpl predSplit | predSplit = predSplits.getASplit() |
      predSplit.hasExitScope(succ, pred, c)
    )
  )
}

/**
 * Internal representation of control flow nodes in the control flow graph.
 * The control flow graph is pruned for unreachable nodes.
 */
cached
newtype TNode =
  TAnnotatedExitNode(Declaration scope, boolean normal) {
    exists(Reachability::SameSplitsBlock b, EdgeKind t | b.isReachable(scope, _) |
      succExitSplits(b.getAnElement(), _, scope, t) and
      if isAbnormalExitType(t) then normal = false else normal = true
    )
  } or
  TInstructionNode(StageInstruction n, Splits splits) {
    exists(Reachability::SameSplitsBlock b, Declaration scope | b.isReachable(scope, splits) |
      n = b.getAnElement()
    )
  }

predicate exitNode(InstructionNode n, Declaration scope) {
  n.getAstNode().(ExitFunctionInstruction).getEnclosingFunction() = scope
}

private predicate isFullyConstructedSplits(Splits splits) { exists(TInstructionNode(_, splits)) }

/**
 * A set of control flow node splits. The set is represented by a list of splits,
 * ordered by ascending rank.
 */
class Splits extends TSplits {
  /** Gets a textual representation of this set of splits. */
  string toString() {
    result = splitsToString(this)
    or
    not isFullyConstructedSplits(this) and
    result = "<partial split set>"
  }

  /** Gets a split belonging to this set of splits. */
  SplitImpl getASplit() {
    exists(SplitImpl head, Splits tail | this = TSplitsCons(head, tail) |
      result = head
      or
      result = tail.getASplit()
    )
  }
}

private predicate entryNode(InstructionNode entry, Declaration scope) {
  entry.getAstNode().(EnterFunctionInstruction).getEnclosingFunction() = scope
}

abstract class Node extends TNode {
  /** Gets a textual representation of this control flow node. */
  pragma[nomagic]
  abstract string toString();

  /** Gets the AST node that this node corresponds to, if any. */
  abstract StageInstruction getAstNode();

  /** Gets the location of this control flow node. */
  pragma[nomagic]
  abstract Location getLocation();

  // /** Holds if this control flow node has conditional successors. */
  // predicate isCondition() { exists(this.getASuccessor(any(EdgeKind t | isCondition(t)))) }
  /** Gets the scope of this node. */
  Declaration getScope() {
    this = TAnnotatedExitNode(result, _)
    or
    exists(StageInstruction i |
      this = TInstructionNode(i, _) and
      result = i.getEnclosingFunction()
    )
  }

  abstract Splits getSplits();

  /** Gets a successor node of a given type, if any. */
  Node getASuccessor(EdgeKind t) { result = getASuccessor(this, t) }

  /** Gets an immediate successor, if any. */
  Node getASuccessor() { result = this.getASuccessor(_) }

  /** Gets an immediate predecessor node of a given flow type, if any. */
  Node getAPredecessor(EdgeKind t) { result.getASuccessor(t) = this }

  /** Gets an immediate predecessor, if any. */
  Node getAPredecessor() { result = this.getAPredecessor(_) }

  /** Holds if this node has more than one predecessor. */
  predicate isJoin() { strictcount(this.getAPredecessor()) > 1 }

  /** Holds if this node has more than one successor. */
  predicate isBranch() { strictcount(this.getASuccessor()) > 1 }
}

/** An exit node for a given scope, annotated with the type of exit. */
class AnnotatedExitNode extends Node, TAnnotatedExitNode {
  private Declaration scope;
  private boolean normal;

  AnnotatedExitNode() { this = TAnnotatedExitNode(scope, normal) }

  /** Holds if this node represent a normal exit. */
  final predicate isNormal() { normal = true }

  final override StageInstruction getAstNode() { none() }

  final override Location getLocation() { result = scope.getLocation() }

  final override string toString() {
    exists(string s |
      normal = true and s = "normal"
      or
      normal = false and s = "abnormal"
    |
      result = "exit " + scope + " (" + s + ")"
    )
  }

  override Splits getSplits() { result = TSplitsNil() }
}

/**
 * A node for an AST node.
 *
 * Each AST node maps to zero or more `InstructionNode`s: zero when the node is unreachable
 * (dead) code or not important for control flow, and multiple when there are different
 * splits for the AST node.
 */
class InstructionNode extends Node, TInstructionNode {
  private Splits splits;
  private StageInstruction n;

  InstructionNode() { this = TInstructionNode(n, splits) }

  final override StageInstruction getAstNode() { result = n }

  override Location getLocation() { result = n.getLocation() }

  final override string toString() {
    exists(string s | s = n.toString() |
      result = "[" + this.getSplitsString() + "] " + s
      or
      not exists(this.getSplitsString()) and result = s
    )
  }

  /** Gets a comma-separated list of strings for each split in this node, if any. */
  final string getSplitsString() {
    result = splits.toString() and
    result != ""
  }

  /** Gets a split for this control flow node, if any. */
  final Split getASplit() { result = splits.getASplit() }

  final override Splits getSplits() { result = splits }
}

/** Gets a successor node of a given flow type, if any. */
cached
Node getASuccessor(Node pred, EdgeKind t) {
  exists(Declaration scope, StageInstruction predElement, Splits predSplits |
    predElement.getEnclosingFunction() = pragma[only_bind_into](scope) and
    pred = TInstructionNode(predElement, predSplits)
  |
    // Element node -> callable exit (annotated)
    exists(boolean normal |
      result = TAnnotatedExitNode(pragma[only_bind_into](scope), normal) and
      succExitSplits(predElement, predSplits, scope, t) and
      if isAbnormalExitType(t) then normal = false else normal = true
    )
    or
    // Element node -> element node
    exists(StageInstruction succElement, Splits succSplits, Completion c |
      succElement.getEnclosingFunction() = pragma[only_bind_into](scope) and
      result = TInstructionNode(succElement, succSplits) and
      SuccSplits::succSplits(predElement, predSplits, succElement, succSplits, _, c, _) and
      t = getAMatchingSuccessorType(c)
    )
  )
  or
  // Callable exit (annotated) -> callable exit
  exists(Declaration scope |
    pred = TAnnotatedExitNode(scope, _) and
    exitNode(result, scope) and
    isSimple(t)
  )
}

TranslatedElement getInstructionTranslatedElement(StageInstruction instruction) {
  instruction = TRawInstruction0(result, _)
}

InstructionTag getInstructionTag(StageInstruction instruction) {
  instruction = TRawInstruction0(_, result)
}

StageInstruction getInstructionSuccessor(StageInstruction instruction, EdgeKind kind, Completion c) {
  exists(TranslatedElement te | te = getInstructionTranslatedElement(instruction) |
    result = te.getInstructionSuccessor(getInstructionTag(instruction), kind, c)
  )
}

module SplittingConsistency {
  /** Holds if `s1` and `s2` are distinct representations of the same set. */
  query predicate nonUniqueSetRepresentation(Splits s1, Splits s2) {
    forex(Split s | s = s1.getASplit() | s = s2.getASplit()) and
    forex(Split s | s = s2.getASplit() | s = s1.getASplit()) and
    s1 != s2
  }

  /** Holds if splitting invariant 2 is violated. */
  query predicate breakInvariant2(
    StageInstruction pred, Splits predSplits, StageInstruction succ, Splits succSplits,
    SplitImpl split, EdgeKind edge, Completion c, string debug
  ) {
    SuccSplits::succSplits(pred, predSplits, succ, succSplits, edge, c, debug) and
    split = predSplits.getASplit() and
    split.hasSuccessor(pred, succ, edge, c) and
    not split = succSplits.getASplit()
  }

  /** Holds if splitting invariant 3 is violated. */
  query predicate breakInvariant3(
    StageInstruction pred, Splits predSplits, StageInstruction succ, Splits succSplits,
    SplitImpl split, EdgeKind edge, Completion c, string debug
  ) {
    SuccSplits::succSplits(pred, predSplits, succ, succSplits, edge, c, debug) and
    split = predSplits.getASplit() and
    split.hasExit(pred, succ, c) and
    not split.hasEntry(pred, succ, c) and
    split = succSplits.getASplit()
  }

  /** Holds if splitting invariant 4 is violated. */
  query predicate breakInvariant4(
    StageInstruction pred, Splits predSplits, StageInstruction succ, Splits succSplits,
    SplitImpl split, EdgeKind edge, Completion c, string debug
  ) {
    SuccSplits::succSplits(pred, predSplits, succ, succSplits, edge, c, debug) and
    split.hasEntry(pred, succ, c) and
    not split.getKind() = predSplits.getASplit().getKind() and
    not split = succSplits.getASplit() and
    split.getKind().isEnabled(succ)
  }

  /** Holds if splitting invariant 5 is violated. */
  query predicate breakInvariant5(
    StageInstruction pred, Splits predSplits, StageInstruction succ, Splits succSplits,
    SplitImpl split, EdgeKind edge, Completion c, string debug
  ) {
    SuccSplits::succSplits(pred, predSplits, succ, succSplits, edge, c, debug) and
    split = succSplits.getASplit() and
    not (split.hasSuccessor(pred, succ, edge, c) and split = predSplits.getASplit()) and
    not split.hasEntry(pred, succ, c)
  }

  /** Holds if `node` is lacking a successor. */
  query predicate deadEnd(Node node) {
    not exitNode(node, _) and
    not exists(getASuccessor(node, _))
  }

  /** Holds if `split` has multiple kinds. */
  query predicate nonUniqueSplitKind(SplitImpl split, SplitKind sk) {
    sk = split.getKind() and
    strictcount(split.getKind()) > 1
  }

  /** Holds if `sk` has multiple integer representations. */
  query predicate nonUniqueListOrder(SplitKind sk, int ord) {
    ord = sk.getListOrder() and
    strictcount(sk.getListOrder()) > 1
  }
}
