private import cpp
private import DataFlowUtil
private import semmle.code.cpp.ir.IR
private import DataFlowDispatch
private import DataFlowImplConsistency
private import SsaInternals as Ssa

/** Gets the callable in which this node occurs. */
DataFlowCallable nodeGetEnclosingCallable(Node n) { result = n.getEnclosingCallable() }

/** Holds if `p` is a `ParameterNode` of `c` with position `pos`. */
predicate isParameterNode(ParameterNode p, DataFlowCallable c, ParameterPosition pos) {
  p.isParameterOf(c, pos)
}

/** Holds if `arg` is an `ArgumentNode` of `c` with position `pos`. */
predicate isArgumentNode(ArgumentNode arg, DataFlowCall c, ArgumentPosition pos) {
  arg.argumentOf(c, pos)
}

/**
 * A data flow node that occurs as the argument of a call and is passed as-is
 * to the callable. Instance arguments (`this` pointer) and read side effects
 * on parameters are also included.
 */
abstract class ArgumentNode extends OperandNode {
  /**
   * Holds if this argument occurs at the given position in the given call.
   * The instance argument is considered to have index `-1`.
   */
  abstract predicate argumentOf(DataFlowCall call, ArgumentPosition pos);

  /** Gets the call in which this node is an argument. */
  DataFlowCall getCall() { this.argumentOf(result, _) }
}

/**
 * A data flow node that occurs as the argument to a call, or an
 * implicit `this` pointer argument.
 */
private class PrimaryArgumentNode extends ArgumentNode {
  ArgumentOperand arg;

  PrimaryArgumentNode() {
    arg = this.getOperand() and exists(CallInstruction call | arg = call.getAnArgumentOperand())
  }

  override predicate argumentOf(DataFlowCall call, ArgumentPosition pos) {
    arg = call.getArgumentOperand(pos.getIndex()) and
    pos.getIndirection() = this.getSSAOperand().getSourceVariable().getIndirection()
  }

  override string toString() {
    exists(Expr unconverted |
      unconverted = arg.getDef().getUnconvertedResultExpression() and
      result = unconverted.toString()
    )
    or
    // Certain instructions don't map to an unconverted result expression. For these cases
    // we fall back to a simpler naming scheme. This can happen in IR-generated constructors.
    not exists(arg.getDef().getUnconvertedResultExpression()) and
    (
      result = "Argument " + arg.(PositionalArgumentOperand).getIndex()
      or
      arg instanceof ThisArgumentOperand and result = "Argument this"
    )
  }
}

/** A parameter position represented by an integer. */
class ParameterPosition = Position;

/** An argument position represented by an integer. */
class ArgumentPosition = Position;

class Position extends TMkPosition {
  int index;
  int ind;

  Position() { this = TMkPosition(index, ind) }

  string toString() {
    exists(string suffix |
      index = -1 and
      suffix = "this"
      or
      index != -1 and
      suffix = index.toString()
    |
      result = "*********".prefix(ind) + suffix
    )
  }

  int getIndex() { result = index }

  int getIndirection() { result = ind }
}

newtype TPosition =
  TMkPosition(int index, int ind) {
    exists(Type type, CallInstruction c |
      c.getArgument(index).getResultLanguageType().hasType(type, _) and
      ind = [0 .. Ssa::getMaxIndirectionsForType(type)]
    )
  }

private newtype TReturnKind =
  TNormalReturnKind() or
  TIndirectReturnKind(ParameterIndex index, int ind) {
    ind = [0 .. 10] // TODO
  }

/**
 * A return kind. A return kind describes how a value can be returned
 * from a callable. For C++, this is simply a function return.
 */
class ReturnKind extends TReturnKind {
  /** Gets a textual representation of this return kind. */
  abstract string toString();
}

private class NormalReturnKind extends ReturnKind, TNormalReturnKind {
  override string toString() { result = "return" }
}

private class IndirectReturnKind extends ReturnKind, TIndirectReturnKind {
  ParameterIndex index;
  int ind;

  IndirectReturnKind() { this = TIndirectReturnKind(index, ind) }

  override string toString() {
    result = "************".prefix(ind) + "outparam[" + index.toString() + "]"
  }
}

newtype TReturnNodeImpl =
  TReturnValueNodeImpl(ReturnValueInstruction ret) or
  TReturnIndirectionNodeImpl(Ssa::SSAOperand operand, ReturnIndirectionInstruction rii) {
    operand.getUse().getInstruction() = rii
  }

/** A data flow node that occurs as the result of a `ReturnStmt`. */
class ReturnNodeImpl extends TReturnNodeImpl {
  abstract string toString();

  /** Gets the kind of this returned value. */
  abstract ReturnKind getKind();

  abstract Function getEnclosingFunction();

  abstract Location getLocation();
}

class ReturnValueNode extends ReturnNodeImpl, TReturnValueNodeImpl {
  ReturnValueInstruction ret;

  ReturnValueNode() { this = TReturnValueNodeImpl(ret) }

  override string toString() { result = ret.toString() }

  override ReturnKind getKind() { result = TNormalReturnKind() }

  override Function getEnclosingFunction() { result = ret.getEnclosingFunction() }

  override Location getLocation() { result = ret.getLocation() }
}

class ReturnIndirectionNode extends ReturnNodeImpl, TReturnIndirectionNodeImpl {
  Ssa::SSAOperand use;
  ReturnIndirectionInstruction rii;

  ReturnIndirectionNode() { this = TReturnIndirectionNodeImpl(use, rii) }

  override string toString() { result = use.toString() }

  override ReturnKind getKind() {
    exists(int index |
      rii.hasIndex(index) and
      result = TIndirectReturnKind(index, use.getSourceVariable().getIndirection())
    )
  }

  override Function getEnclosingFunction() { result = rii.getEnclosingFunction() }

  override Location getLocation() { result = rii.getLocation() }
}

newtype TOutNodeImpl =
  TCallOutNodeImpl(CallInstruction call) or
  TSideEffectOutNodeImpl(Ssa::SSADefInstruction def, WriteSideEffectInstruction write) {
    write = def.getInstruction()
  }

/** A data flow node that represents the output of a call. */
class OutNodeImpl extends TOutNodeImpl {
  /** Gets the underlying call. */
  abstract DataFlowCall getCall();

  abstract string toString();

  abstract ReturnKind getReturnKind();

  abstract Function getEnclosingFunction();

  abstract Location getLocation();
}

private class CallOutNode extends OutNodeImpl, TCallOutNodeImpl {
  CallInstruction instr;

  CallOutNode() { this = TCallOutNodeImpl(instr) }

  override string toString() { result = instr.toString() }

  override DataFlowCall getCall() { result = instr }

  override ReturnKind getReturnKind() { result instanceof NormalReturnKind }

  override Function getEnclosingFunction() { result = instr.getEnclosingFunction() }

  override Location getLocation() { result = instr.getLocation() }
}

private class SideEffectOutNode extends OutNodeImpl, TSideEffectOutNodeImpl {
  Ssa::SSADefInstruction instr;
  WriteSideEffectInstruction write;

  SideEffectOutNode() { this = TSideEffectOutNodeImpl(instr, write) }

  override string toString() { result = instr.toString() }

  override DataFlowCall getCall() { result = write.getPrimaryInstruction() }

  override ReturnKind getReturnKind() {
    result = TIndirectReturnKind(write.getIndex(), instr.getSourceVariable().getIndirection())
  }

  override Function getEnclosingFunction() { result = write.getEnclosingFunction() }

  override Location getLocation() { result = write.getLocation() }
}

/**
 * Gets a node that can read the value returned from `call` with return kind
 * `kind`.
 */
OutNode getAnOutNode(DataFlowCall call, ReturnKind kind) {
  // There should be only one `OutNode` for a given `(call, kind)` pair. Showing the optimizer that
  // this is true helps it make better decisions downstream, especially in virtual dispatch.
  result =
    unique(OutNode outNode |
      outNode.getCall() = call and
      outNode.getReturnKind() = kind
    )
}

/**
 * Holds if data can flow from `node1` to `node2` in a way that loses the
 * calling context. For example, this would happen with flow through a
 * global or static variable.
 */
predicate jumpStep(Node n1, Node n2) { none() }

int indirectionsUntilFirstFieldAddress(Instruction i) {
  exists(Instruction i0, boolean hasFieldOffset | Ssa::conversionFlow(i0, i, hasFieldOffset) |
    if hasFieldOffset = true then result = 0 else result = indirectionsUntilFirstFieldAddress(i0)
  )
  or
  result = 1 + indirectionsUntilFirstFieldAddress(i.(LoadInstruction).getSourceAddress())
}

/**
 * Holds if data can flow from `node1` to `node2` via an assignment to `f`.
 * Thus, `node2` references an object with a field `f` that contains the
 * value of `node1`.
 */
predicate storeStep(Node node1, FieldContent f, PostFieldUpdateNode node2) {
  // This is the first field following a store operation.
  not isNextFieldAddress(node2.getFieldAddressInstruction(), _) and
  exists(StoreInstruction store |
    store = node1.asInstruction() and
    store = node2.getInstruction() and
    f.getIndirection() = indirectionsUntilFirstFieldAddress(store.getDestinationAddress()) and
    f.getField() = node2.getFieldAddressInstruction().getField()
  )
  or
  exists(FieldAddressInstruction fai1, FieldAddressInstruction fai2 |
    node1.(PostFieldUpdateNode).getFieldAddressInstruction() = fai1 and
    node2.getFieldAddressInstruction() = fai2 and
    isNextFieldAddress(fai2, fai1) and
    f.getField() = fai2.getField() and
    // TODO: I think - 1 should be generalized
    f.getIndirection() =
      node1.(PostFieldUpdateNode).getSsaInstruction().getSourceVariable().getIndirection() - 1
  )
}

Ssa::SourceVariable decrementMany(Ssa::SourceVariable sv, int n) {
  n = [0 .. Ssa::getMaxIndirectionsForType(_)] and
  (
    n = 0 and
    result = sv
    or
    n > 0 and
    result = decrementMany(sv.decrementIndirection(), n - 1)
  )
}

/**
 * Holds if data can flow from `node1` to `node2` via a read of `f`.
 * Thus, `node1` references an object with a field `f` whose value ends up in
 * `node2`.
 */
predicate readStep(Node node1, FieldContent f, Node node2) {
  exists(
    Ssa::SSAInstruction ssaInstr, FieldAddressInstruction fai, Ssa::SSAOperand ssaOperand,
    Ssa::SSAOperand ssaOperand2
  |
    ssaOperand = node1.(OperandNode).getSSAOperand() and
    ssaInstr.getAnOperand() = ssaOperand and
    ssaInstr.getInstruction() = fai and
    f.getIndirection() = ssaOperand.getSourceVariable().getIndirection() and
    f.getField() = fai.getField() and
    ssaOperand2.getOperand() = ssaOperand.getOperand() and
    ssaOperand2.getSourceVariable() =
      decrementMany(ssaOperand.getSourceVariable(), f.getIndirection()) and
    Ssa::defUseFlow(ssaOperandNode(ssaOperand2), node2)
  )
}

/**
 * Holds if values stored inside content `c` are cleared at node `n`.
 */
predicate clearsContent(Node n, Content c) {
  none() // stub implementation
}

/** Gets the type of `n` used for type pruning. */
IRType getNodeType(Node n) {
  suppressUnusedNode(n) and
  result instanceof IRVoidType // stub implementation
}

/** Gets a string representation of a type returned by `getNodeType`. */
string ppReprType(IRType t) { none() } // stub implementation

/**
 * Holds if `t1` and `t2` are compatible, that is, whether data can flow from
 * a node of type `t1` to a node of type `t2`.
 */
pragma[inline]
predicate compatibleTypes(IRType t1, IRType t2) {
  any() // stub implementation
}

private predicate suppressUnusedNode(Node n) { any() }

//////////////////////////////////////////////////////////////////////////////
// Java QL library compatibility wrappers
//////////////////////////////////////////////////////////////////////////////
/** A node that performs a type cast. */
class CastNode extends Node {
  CastNode() { none() } // stub implementation
}

/**
 * A function that may contain code or a variable that may contain itself. When
 * flow crosses from one _enclosing callable_ to another, the interprocedural
 * data-flow library discards call contexts and inserts a node in the big-step
 * relation used for human-readable path explanations.
 */
class DataFlowCallable = Declaration;

class DataFlowExpr = Expr;

class DataFlowType = IRType;

/** A function call relevant for data flow. */
class DataFlowCall extends CallInstruction {
  Function getEnclosingCallable() { result = this.getEnclosingFunction() }
}

predicate isUnreachableInCall(Node n, DataFlowCall call) { none() } // stub implementation

int accessPathLimit() { result = 5 }

/**
 * Holds if access paths with `c` at their head always should be tracked at high
 * precision. This disables adaptive access path precision for such access paths.
 */
predicate forceHighPrecision(Content c) { none() }

/** The unit type. */
private newtype TUnit = TMkUnit()

/** The trivial type with a single element. */
class Unit extends TUnit {
  /** Gets a textual representation of this element. */
  string toString() { result = "unit" }
}

/** Holds if `n` should be hidden from path explanations. */
predicate nodeIsHidden(Node n) { n instanceof OperandNode and not n instanceof ArgumentNode }

class LambdaCallKind = Unit;

/** Holds if `creation` is an expression that creates a lambda of kind `kind` for `c`. */
predicate lambdaCreation(Node creation, LambdaCallKind kind, DataFlowCallable c) { none() }

/** Holds if `call` is a lambda call of kind `kind` where `receiver` is the lambda expression. */
predicate lambdaCall(DataFlowCall call, LambdaCallKind kind, Node receiver) { none() }

/** Extra data-flow steps needed for lambda flow analysis. */
predicate additionalLambdaFlowStep(Node nodeFrom, Node nodeTo, boolean preservesValue) { none() }

/**
 * Holds if flow is allowed to pass from parameter `p` and back to itself as a
 * side-effect, resulting in a summary from `p` to itself.
 *
 * One example would be to allow flow like `p.foo = p.bar;`, which is disallowed
 * by default as a heuristic.
 */
predicate allowParameterReturnInSelf(ParameterNode p) { none() }

private class MyConsistencyConfiguration extends Consistency::ConsistencyConfiguration {
  override predicate argHasPostUpdateExclude(ArgumentNode n) {
    // The rules for whether an IR argument gets a post-update node are too
    // complex to model here.
    any()
  }
}

private predicate step(Node node1, Node node2, string msg) {
  stepFwd(_, node1) and
  (
    simpleLocalFlowStep(node1, node2) and msg = ""
    or
    exists(Content c, string after | after = c.toString() |
      readStep(node1, c, node2) and msg = "Read " + after
      or
      storeStep(node1, c, node2) and msg = "Store " + after
    )
    // or
    // exists(CallInstruction call, ParameterPosition pos |
    //   node1.(ArgumentNode).argumentOf(call, pos) and
    //   node2.(ParameterNode).isParameterOf(call.getStaticCallTarget(), pos) and
    //   msg = "into"
    // )
    // or
    // exists(OutNode out, ReturnKind kind |
    //   out = node2 and
    //   node1.(ReturnNode).getKind() = kind and
    //   out.getReturnKind() = kind and
    //   node1.getEnclosingCallable() = out.getCall().getStaticCallTarget() and
    //   msg = kind.toString()
    // )
  )
}

private predicate stepFwd(Node node1, Node node2) {
  // stepRev(node1, _, _, _) and
  // stepRev(node2, _, _, _) and
  (
    node1 = node2 and
    node1.asExpr().(Call).getTarget().hasName("source")
    or
    exists(Node mid |
      stepFwd(node1, mid) and
      step(mid, node2, _)
    )
  )
}

private predicate stepRev(Node node1, Node node2) {
  stepFwd(_, node1) and
  stepFwd(_, node2) and
  (
    node1 = node2 and
    [node2.asExpr()] = any(Call call | call.getTarget().hasName("sink")).getAnArgument()
    or
    exists(Node mid |
      stepRev(mid, node2) and
      step(node1, mid, _)
    )
  )
}

private predicate step2(Node node1, Node node2, string msg) {
  stepRev(node1, _) and
  (
    simpleLocalFlowStep(node1, node2) and msg = ""
    or
    exists(Content c, string after | after = c.toString() |
      readStep(node1, c, node2) and msg = "Read " + after
      or
      storeStep(node1, c, node2) and msg = "Store " + after
    )
    // or
    // exists(CallInstruction call, ParameterPosition pos |
    //   node1.(ArgumentNode).argumentOf(call, pos) and
    //   node2.(ParameterNode).isParameterOf(call.getStaticCallTarget(), pos) and
    //   msg = "into"
    // )
    // or
    // exists(OutNode out, ReturnKind kind |
    //   out = node2 and
    //   node1.(ReturnNode).getKind() = kind and
    //   out.getReturnKind() = kind and
    //   node1.getEnclosingCallable() = out.getCall().getStaticCallTarget() and
    //   msg = kind.toString()
    // )
  )
}
