/**
 * Provides predicates for giving improved type bounds on expressions.
 *
 * An inferred bound on the runtime type of an expression can be either exact
 * or merely an upper bound. Bounds are only reported if they are likely to be
 * better than the static bound, which can happen either if an inferred exact
 * type has a subtype or if an inferred upper bound passed through at least one
 * explicit or implicit cast that lost type information.
 */

private import cpp as Cpp
private import semmle.code.cpp.ir.IR
private import DataFlowPrivate

newtype TTrackedType =
  TArrayType() or
  TObjectType()

class TrackedType extends TTrackedType {
  string toString() { none() }

  predicate hasExactType(Instruction i) { none() }

  /** Gets a direct supertype of this type. */
  TrackedType getASupertype() { none() }

  /** Gets a direct subtype of this type. */
  final TrackedType getASubtype() { this = result.getASupertype() }

  /** Gets a direct or indirect descendant of this type, including itself. */
  final TrackedType getADescendant() {
    result = this
    or
    exists(TrackedType mid | this.getASubtype() = mid and result = mid.getADescendant())
  }

  /** Gets a direct or indirect supertype of this type, including itself. */
  final TrackedType getAnAncestor() { this = result.getADescendant() }

  /**
   * Gets a direct or indirect supertype of this type.
   * This does not include itself, unless this type is part of a cycle
   * in the type hierarchy.
   */
  final TrackedType getAStrictAncestor() { result = this.getASupertype().getAnAncestor() }
}

class ArrayType extends TArrayType, TrackedType {
  override string toString() { result = "ArrayType" }

  override predicate hasExactType(Instruction i) {
    not any(ObjectType t).hasExactType(i) and
    (
      i.getResultType() instanceof Cpp::ArrayType
      or
      exists(Cpp::AllocationExpr alloc | alloc = i.getUnconvertedResultExpression())
      or
      exists(CallInstruction call, Cpp::Function func |
        call = i and
        call.getResultType() instanceof Cpp::PointerType and
        func = call.getStaticCallTarget() and
        not exists(func.getEntryPoint())
      )
    )
  }
}

class ObjectType extends TObjectType, TrackedType {
  override string toString() { result = "ObjectType" }

  override predicate hasExactType(Instruction i) {
    // A non-array variable
    i instanceof VariableAddressInstruction and
    not i.getResultType() instanceof Cpp::ArrayType
    or
    i.getResultType() instanceof Cpp::ReferenceType
    or
    // this is never an array
    i instanceof InitializeThisInstruction
    or
    // An allocation of a non-array object
    exists(Cpp::AllocationExpr alloc | alloc = i.getUnconvertedResultExpression() |
      // i.e., `new int`;
      alloc instanceof Cpp::NewExpr
      or
      // i.e., `malloc(sizeof(int))`
      exists(Cpp::SizeofTypeOperator sizeOf | sizeOf = alloc.getSizeExpr() |
        not sizeOf.getTypeOperand().getUnspecifiedType() instanceof Cpp::ArrayType
      )
    )
  }

  override TrackedType getASupertype() { result instanceof ArrayType }
}

newtype TTypeFlowNode =
  TInstruction(Instruction instr) or
  TFunction(IRFunction func)

/**
 * A `Field`, `BaseSsaVariable`, `Expr`, or `Method`.
 */
private class TypeFlowNode extends TTypeFlowNode {
  string toString() {
    result = this.asInstruction().toString()
    or
    result = this.asFunction().toString()
  }

  Cpp::Location getLocation() {
    result = this.asInstruction().getLocation()
    or
    result = this.asFunction().getLocation()
  }

  Instruction asInstruction() { this = TInstruction(result) }

  IRFunction asFunction() { this = TFunction(result) }

  TrackedType getType() {
    result.hasExactType(this.asInstruction())
    or
    result
        .hasExactType(this.asFunction()
              .getReturnInstruction()
              .(ReturnValueInstruction)
              .getReturnValue())
  }
}

private Instruction getAnUltimateLocalDefinition(PhiInstruction phi) {
  result = phi.getAnInput*() and not result instanceof PhiInstruction
}

/**
 * Holds if this function is private (i.e., cannot be accessed outside it's compilation unit).
 * This means we can use a closed-world assumption about calls to this function.
 */
private predicate isPrivate(Cpp::Function func) {
  func.isStatic()
  or
  func.getNamespace().getParentNamespace*().isInline()
  or
  func.(Cpp::MemberFunction).isPrivate()
}

/**
 * Holds if `arg` is an argument for the parameter `p` in a private callable.
 */
pragma[nomagic]
private predicate privateParamArg(InitializeParameterInstruction p, Instruction arg) {
  exists(CallInstruction call, int i, Cpp::Function func |
    call.getArgument(pragma[only_bind_into](i)) = arg and
    func = call.getStaticCallTarget() and
    func.getParameter(pragma[only_bind_into](i)) = p.getParameter() and
    isPrivate(func)
  )
}

/**
 * Holds if data can flow from `n1` to `n2` in one step, and `n1` is not
 * necessarily functionally determined by `n2`.
 */
private predicate joinStep0(TypeFlowNode n1, TypeFlowNode n2) {
  getAnUltimateLocalDefinition(n2.asInstruction()) = n1.asInstruction()
  or
  // Instruction -> Function
  exists(ReturnInstruction ret |
    n2.asFunction() = ret.getEnclosingIRFunction() and ret = n1.asInstruction()
  )
  or
  // Function -> Instruction
  n2.asInstruction().(CallInstruction).getStaticCallTarget() = n1.asFunction().getFunction()
  or
  // Into "private" functions
  exists(Instruction arg, Instruction p |
    privateParamArg(p, arg) and
    n1.asInstruction() = arg and
    n2.asInstruction() = p
  )
}

/**
 * Holds if data can flow from `n1` to `n2` in one step, and `n1` is
 * functionally determined by `n2`.
 */
private predicate step(TypeFlowNode n1, TypeFlowNode n2) {
  n2.asInstruction().(CopyInstruction).getSourceValue() = n1.asInstruction()
  or
  n2.asInstruction().(ConvertInstruction).getUnary() = n1.asInstruction()
  or
  n2.asInstruction().(CheckedConvertOrNullInstruction).getUnary() = n1.asInstruction()
  or
  n2.asInstruction().(InheritanceConversionInstruction).getUnary() = n1.asInstruction()
  or
  // Note: This isn't actually functional, but the _type_ of n2 is functionally
  // determined by the type of n1.
  n2.asInstruction().(PointerOffsetInstruction).getLeft() = n1.asInstruction()
}

/**
 * Holds if `null` is the only value that flows to `n`.
 */
private predicate isNull(TypeFlowNode n) {
  n.asInstruction().(ConstantInstruction).getValue() = "0" and
  n.asInstruction().getResultIRType() instanceof IRAddressType
  or
  exists(TypeFlowNode mid | isNull(mid) and step(mid, n))
  or
  forex(TypeFlowNode mid | joinStep0(mid, n) | isNull(mid))
}

/**
 * Holds if data can flow from `n1` to `n2` in one step, `n1` is not necessarily
 * functionally determined by `n2`, and `n1` might take a non-null value.
 */
private predicate joinStep(TypeFlowNode n1, TypeFlowNode n2) {
  joinStep0(n1, n2) and not isNull(n1)
}

private predicate anyStep(TypeFlowNode n1, TypeFlowNode n2) { joinStep(n1, n2) or step(n1, n2) }

private predicate sccEdge(TypeFlowNode n1, TypeFlowNode n2) { anyStep(n1, n2) and anyStep+(n2, n1) }

private module Scc = QlBuiltins::EquivalenceRelation<TypeFlowNode, sccEdge/2>;

private class TypeFlowScc = Scc::EquivalenceClass;

/** Holds if `n` is part of an SCC of size 2 or more represented by `scc`. */
private predicate sccRepr(TypeFlowNode n, TypeFlowScc scc) { scc = Scc::getEquivalenceClass(n) }

private predicate sccJoinStep(TypeFlowNode n, TypeFlowScc scc) {
  exists(TypeFlowNode mid |
    joinStep(n, mid) and
    sccRepr(mid, scc) and
    not sccRepr(n, scc)
  )
}

private signature class NodeSig;

private signature module Edge {
  class Node;

  predicate edge(TypeFlowNode n1, Node n2);
}

private signature module RankedEdge<NodeSig Node> {
  predicate edgeRank(int r, TypeFlowNode n1, Node n2);

  int lastRank(Node n);
}

private module RankEdge<Edge E> implements RankedEdge<E::Node> {
  private import E

  /**
   * Holds if `r` is a ranking of the incoming edges `(n1,n2)` to `n2`. The used
   * ordering is not necessarily total, so the ranking may have gaps.
   */
  private predicate edgeRank1(int r, TypeFlowNode n1, Node n2) {
    n1 =
      rank[r](TypeFlowNode n |
        edge(n, n2)
      |
        n order by n.getLocation().getStartLine(), n.getLocation().getStartColumn()
      )
  }

  /**
   * Holds if `r2` is a ranking of the ranks from `edgeRank1`. This removes the
   * gaps from the ranking.
   */
  private predicate edgeRank2(int r2, int r1, Node n) {
    r1 = rank[r2](int r | edgeRank1(r, _, n) | r)
  }

  /** Holds if `r` is a ranking of the incoming edges `(n1,n2)` to `n2`. */
  predicate edgeRank(int r, TypeFlowNode n1, Node n2) {
    exists(int r1 |
      edgeRank1(r1, n1, n2) and
      edgeRank2(r, r1, n2)
    )
  }

  int lastRank(Node n) { result = max(int r | edgeRank(r, _, n)) }
}

private signature module TypePropagation {
  class Typ;

  predicate candType(TypeFlowNode n, Typ t);

  bindingset[t]
  predicate supportsType(TypeFlowNode n, Typ t);
}

/** Implements recursion through `forall` by way of edge ranking. */
private module ForAll<NodeSig Node, RankedEdge<Node> E, TypePropagation T> {
  /**
   * Holds if `t` is a bound that holds on one of the incoming edges to `n` and
   * thus is a candidate bound for `n`.
   */
  pragma[nomagic]
  private predicate candJoinType(Node n, T::Typ t) {
    exists(TypeFlowNode mid |
      T::candType(mid, t) and
      E::edgeRank(_, mid, n)
    )
  }

  /**
   * Holds if `t` is a candidate bound for `n` that is also valid for data coming
   * through the edges into `n` ranked from `1` to `r`.
   */
  private predicate flowJoin(int r, Node n, T::Typ t) {
    (
      r = 1 and candJoinType(n, t)
      or
      flowJoin(r - 1, n, t) and E::edgeRank(r, _, n)
    ) and
    forall(TypeFlowNode mid | E::edgeRank(r, mid, n) | T::supportsType(mid, t))
  }

  /**
   * Holds if `t` is a candidate bound for `n` that is also valid for data
   * coming through all the incoming edges, and therefore is a valid bound for
   * `n`.
   */
  predicate flowJoin(Node n, T::Typ t) { flowJoin(E::lastRank(n), n, t) }
}

private module JoinStep implements Edge {
  class Node = TypeFlowNode;

  predicate edge = joinStep/2;
}

private module SccJoinStep implements Edge {
  class Node = TypeFlowScc;

  predicate edge = sccJoinStep/2;
}

private module RankedJoinStep = RankEdge<JoinStep>;

private module RankedSccJoinStep = RankEdge<SccJoinStep>;

private predicate exactTypeBase(TypeFlowNode n, TrackedType t) { t.hasExactType(n.asInstruction()) }

private module ExactTypePropagation implements TypePropagation {
  class Typ = TrackedType;

  predicate candType = exactType/2;

  predicate supportsType = exactType/2;
}

/**
 * Holds if the runtime type of `n` is exactly `t` and if this bound is a
 * non-trivial lower bound, that is, `t` has a subtype.
 */
private predicate exactType(TypeFlowNode n, TrackedType t) {
  exactTypeBase(n, t)
  or
  exists(TypeFlowNode mid | exactType(mid, t) and step(mid, n))
  or
  // The following is an optimized version of
  // `forex(TypeFlowNode mid | joinStep(mid, n) | exactType(mid, t))`
  ForAll<TypeFlowNode, RankedJoinStep, ExactTypePropagation>::flowJoin(n, t)
  or
  exists(TypeFlowScc scc |
    sccRepr(n, scc) and
    // Optimized version of
    // `forex(TypeFlowNode mid | sccJoinStep(mid, scc) | exactType(mid, t))`
    ForAll<TypeFlowScc, RankedSccJoinStep, ExactTypePropagation>::flowJoin(scc, t)
  )
}

/**
 * Holds if `n` has type `t` and this information is discarded, such that `t`
 * might be a better type bound for nodes where `n` flows to. This might include
 * multiple bounds for a single node.
 */
private predicate typeFlowBaseCand(TypeFlowNode n, TrackedType t) {
  exists(TrackedType srctype |
    exactTypeBase(n, t) and
    t = srctype.getASupertype*()
  )
}

/**
 * Holds if `n` has type `t` and this information is discarded, such that `t`
 * might be a better type bound for nodes where `n` flows to. This only includes
 * the best such bound for each node.
 */
private predicate typeFlowBase(TypeFlowNode n, TrackedType t) {
  typeFlowBaseCand(n, t) and
  not exists(TrackedType better |
    typeFlowBaseCand(n, better) and
    better != t and
    not t.getASupertype+() = better
  |
    better.getASupertype+() = t
  )
}

/**
 * Holds if the runtime type of `n` is bounded by `t` and if this bound is
 * likely to be better than the static type of `n`.
 */
private predicate typeFlow(TypeFlowNode n, TrackedType t) {
  typeFlowBase(n, t)
  or
  exists(TypeFlowNode mid | typeFlow(mid, t) and step(mid, n))
  or
  ForAll<TypeFlowNode, RankedJoinStep, TypeFlowPropagation>::flowJoin(n, t)
  or
  exists(TypeFlowScc scc |
    sccRepr(n, scc) and
    ForAll<TypeFlowScc, RankedSccJoinStep, TypeFlowPropagation>::flowJoin(scc, t)
  )
}

private module TypeFlowPropagation implements TypePropagation {
  class Typ = TrackedType;

  predicate candType = typeFlow/2;

  bindingset[t]
  predicate supportsType(TypeFlowNode mid, TrackedType t) {
    exists(TrackedType midtyp | exactType(mid, midtyp) or typeFlow(mid, midtyp) |
      pragma[only_bind_out](midtyp).getAnAncestor() = t
    )
  }
}

pragma[nomagic]
private predicate typeBound(TrackedType t) { typeFlow(_, t) }

/**
 * Holds if we have a bound for `n` that is better than `t`.
 */
pragma[nomagic]
private predicate irrelevantBound(TypeFlowNode n, TrackedType t) {
  exists(TrackedType bound |
    typeFlow(n, bound) and
    t = bound.getAStrictAncestor() and
    typeBound(t) and
    typeFlow(n, pragma[only_bind_into](t)) and
    not t.getAnAncestor() = bound
    or
    n.getType() = pragma[only_bind_into](bound) and
    typeFlow(n, t) and
    t = bound.getAnAncestor()
  )
}

/**
 * Holds if the runtime type of `n` is bounded by `t`, if this bound is likely
 * to be better than the static type of `n`, and if this the best such bound.
 */
private predicate bestTypeFlow(TypeFlowNode n, TrackedType t) {
  typeFlow(n, t) and
  not irrelevantBound(n, t)
}

private predicate bestTypeFlow(TypeFlowNode n, TrackedType t, boolean exact) {
  exactType(n, t) and exact = true
  or
  not exactType(n, _) and bestTypeFlow(n, t) and exact = false
}

cached
private module TypeFlowBounds {
  /**
   * Holds if the runtime type of `e` is bounded by `t` and if this bound is
   * likely to be better than the static type of `e`. The flag `exact` indicates
   * whether `t` is an exact bound or merely an upper bound.
   */
  cached
  predicate exprTypeFlow(Instruction instr, TrackedType t, boolean exact) {
    exists(TypeFlowNode n |
      n.asInstruction() = instr and
      bestTypeFlow(n, t, exact)
    )
  }

  cached
  predicate isObjectLike(Instruction instr, boolean exact) {
    exprTypeFlow(instr, any(ObjectType ot), exact)
  }
}

import TypeFlowBounds
