private import cpp as Cpp
private import DataFlowUtil
private import semmle.code.cpp.ir.IR
private import DataFlowDispatch
private import semmle.code.cpp.ir.internal.IRCppLanguage
private import semmle.code.cpp.dataflow.internal.FlowSummaryImpl as FlowSummaryImpl
private import DataFlowImplCommon as DataFlowImplCommon
private import codeql.util.Unit
private import ModelUtil
private import semmle.code.cpp.models.interfaces.FunctionInputsAndOutputs as IO
private import semmle.code.cpp.models.interfaces.DataFlow as DF
private import semmle.code.cpp.dataflow.ExternalFlow as External
private import Stage2
private import Stage1
private import Stage0
private import Base

/**
 * The IR dataflow graph consists of the following nodes:
 * - `Node0`, which injects most instructions and operands directly into the
 *    dataflow graph.
 * - `VariableNode`, which is used to model flow through global variables.
 * - `PostUpdateNodeImpl`, which is used to model the state of an object after
 *    an update after a number of loads.
 * - `SsaPhiNode`, which represents phi nodes as computed by the shared SSA
 *    library.
 * - `RawIndirectOperand`, which represents the value of `operand` after
 *    loading the address a number of times.
 * - `RawIndirectInstruction`, which represents the value of `instr` after
 *    loading the address a number of times.
 */
cached
newtype TNode =
  TNode2(Stage2::Node node) { DataFlowImplCommon::forceCachingInSameStage() } or
  TGlobalLikeVariableNode(GlobalLikeVariable var, int indirectionIndex) {
    indirectionIndex =
      [getMinIndirectionsForType(var.getUnspecifiedType()) .. Stage0Output::getMaxIndirectionsForType(var.getUnspecifiedType())]
  } or
  TSsaIteratorNode(IteratorFlow::IteratorFlowNode n) or
  TBodyLessParameterNodeImpl(Parameter p, int indirectionIndex) {
    // Rule out parameters of catch blocks.
    not exists(p.getCatchBlock()) and
    // We subtract one because `getMaxIndirectionsForType` returns the maximum
    // indirection for a glvalue of a given type, and this doesn't apply to
    // parameters.
    indirectionIndex = [0 .. Stage0Output::getMaxIndirectionsForType(p.getUnspecifiedType()) - 1] and
    not any(InitializeParameterInstruction init).getParameter() = p
  } or
  TFlowSummaryNode(FlowSummaryImpl::Private::SummaryNode sn)

/**
 * Gets an additional term that is added to the `join` and `branch` computations to reflect
 * an additional forward or backwards branching factor that is not taken into account
 * when calculating the (virtual) dispatch cost.
 *
 * Argument `arg` is part of a path from a source to a sink, and `p` is the target parameter.
 */
pragma[nomagic]
cached
int getAdditionalFlowIntoCallNodeTerm(ArgumentNode arg, ParameterNode p) {
  DataFlowImplCommon::forceCachingInSameStage() and
  exists(ParameterNode switchee, SwitchInstruction switch, ConditionOperand op, DataFlowCall call |
    DataFlowImplCommon::viableParamArg(call, p, arg) and
    DataFlowImplCommon::viableParamArg(call, switchee, _) and
    switch.getExpressionOperand() = op and
    getAdditionalFlowIntoCallNodeTermStep+(switchee, operandNode(op)) and
    result = countNumberOfBranchesUsingParameter(switch, p)
  )
}

/**
 * A class that lifts pre-SSA dataflow nodes to regular dataflow nodes.
 */
class Node2 extends Node, TNode2 {
  Stage2::Node node;

  Node2() { this = TNode2(node) }

  override Declaration getEnclosingCallable() { result = node.getEnclosingCallable() }

  override Declaration getFunction() { result = node.getFunction() }

  override Location getLocationImpl() { result = node.getLocation() }

  override string toStringImpl() { result = node.toString() }

  override DataFlowType getType() { result = node.getType() }

  override predicate isGLValue() { node.isGLValue() }
}

/**
 * A module for calculating the number of stars (i.e., `*`s) needed for various
 * dataflow node `toString` predicates.
 */
module NodeStars {
  /**
   * Gets the number of stars (i.e., `*`s) needed to produce the `toString`
   * output for `n`.
   */
  string stars(Node node) {
    exists(Stage2::Node n |
      node = TNode2(n) and
      result = n.stars()
    )
    or
    exists(int k |
      k = node.(VariableNode).getIndirectionIndex()
      or
      k = node.(BodyLessParameterNodeImpl).getIndirectionIndex()
    |
      result = repeatStars(k)
    )
  }
}

import NodeStars

/**
 * A data flow node that occurs as the argument of a call and is passed as-is
 * to the callable. Instance arguments (`this` pointer) and read side effects
 * on parameters are also included.
 */
abstract class ArgumentNode extends Node {
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
private class Stage1ArgumentNode extends ArgumentNode, Node2 {
  override Stage2::ArgumentNode node;

  override predicate argumentOf(DataFlowCall call, ArgumentPosition pos) {
    node.argumentOf(call.asCallInstruction(), pos)
  }
}

/**
 * An argument node that is part of a summary. These only occur when the
 * summary contains a synthesized call.
 */
class SummaryArgumentNode extends ArgumentNode, FlowSummaryNode {
  private SummaryCall call_;
  private ArgumentPosition pos_;

  SummaryArgumentNode() {
    FlowSummaryImpl::Private::summaryArgumentNode(call_.getReceiver(), this.getSummaryNode(), pos_)
  }

  override predicate argumentOf(DataFlowCall call, ArgumentPosition pos) {
    call = call_ and
    pos = pos_
  }
}

/** A parameter position represented by an integer. */
class ParameterPosition = Stage1::Position;

/** An argument position represented by an integer. */
class ArgumentPosition = Stage1::Position;

class ReturnKind = Stage2::ReturnKind;

/** A data flow node that occurs as the result of a `ReturnStmt`. */
abstract class ReturnNode extends Node {
  /** Gets the kind of this returned value. */
  abstract ReturnKind getKind();
}

/**
 * A return node that is part of a summary.
 */
private class SummaryReturnNode extends ReturnNode, FlowSummaryNode {
  private ReturnKind rk;

  SummaryReturnNode() { FlowSummaryImpl::Private::summaryReturnNode(this.getSummaryNode(), rk) }

  override ReturnKind getKind() { result = rk }
}

/**
 * A data flow node that represents the output of a call (for example, a
 * return value) at the call site.
 */
class OutNode extends Node {
  OutNode() {
    this = TNode2(any(Stage2::OutNode out))
    or
    // Summary node
    FlowSummaryImpl::Private::summaryOutNode(_, this.(FlowSummaryNode).getSummaryNode(), _)
  }

  /** Gets the underlying call. */
  abstract DataFlowCall getCall();

  /** Gets the kind of this out node. */
  abstract ReturnKind getReturnKind();
}

class CallOutNode extends OutNode, Node2 {
  override Stage2::OutNode node;

  override DataFlowCall getCall() { result.asCallInstruction() = node.getCall() }

  int getIndirectionIndex() { result = node.getReturnKind().getIndirectionIndex() }

  override ReturnKind getReturnKind() { result = node.getReturnKind() }
}

/**
 * An output node that is part of a summary. An output node is needed when the
 * model contains a synthesized call (`SummaryCall`) and the return value of
 * that call is needed by the summary (for example when the model has flow from
 * `Argument[0].ReturnValue`).
 */
private class SummaryOutNode extends OutNode, FlowSummaryNode {
  private SummaryCall call;
  private ReturnKind kind_;

  SummaryOutNode() {
    FlowSummaryImpl::Private::summaryOutNode(call.getReceiver(), this.getSummaryNode(), kind_)
  }

  override DataFlowCall getCall() { result = call }

  override ReturnKind getReturnKind() { result = kind_ }
}

/**
 * Gets a node that can read the value returned from `call` with return kind
 * `kind`.
 */
OutNode getAnOutNode(DataFlowCall call, ReturnKind kind) {
  result.getCall() = call and
  result.getReturnKind() = kind
}

private int getMinIndirectionForGlobalUse(Stage2::GlobalUse use) {
  result = getMinIndirectionsForType(use.getUnspecifiedType())
}

private int getMinIndirectionForGlobalDef(Stage2::GlobalDef def) {
  result = getMinIndirectionsForType(def.getUnspecifiedType())
}

private class FinalGlobalValue extends Node2 {
  override Stage2::FinalGlobalValue node;

  Stage2::GlobalUse getGlobalUse() { result = node.getGlobalUse() }
}

private class InitialGlobalValue extends Node2 {
  override Stage2::InitialGlobalValue node;

  Stage2::GlobalDef getGlobalDef() { result = node.getGlobalDef() }
}

/**
 * Holds if data can flow from `node1` to `node2` in a way that loses the
 * calling context. For example, this would happen with flow through a
 * global or static variable.
 */
predicate jumpStep(Node n1, Node n2) {
  exists(GlobalLikeVariable v |
    exists(Stage2::GlobalUse globalUse |
      v = globalUse.getVariable() and
      n1.(FinalGlobalValue).getGlobalUse() = globalUse
    |
      globalUse.getIndirection() = getMinIndirectionForGlobalUse(globalUse) and
      v = n2.asVariable()
      or
      v = n2.asIndirectVariable(globalUse.getIndirection())
    )
    or
    exists(Stage2::GlobalDef globalDef |
      v = globalDef.getVariable() and
      n2.(InitialGlobalValue).getGlobalDef() = globalDef
    |
      globalDef.getIndirection() = getMinIndirectionForGlobalDef(globalDef) and
      v = n1.asVariable()
      or
      v = n1.asIndirectVariable(globalDef.getIndirection())
    )
  )
  or
  // models-as-data summarized flow
  FlowSummaryImpl::Private::Steps::summaryJumpStep(n1.(FlowSummaryNode).getSummaryNode(),
    n2.(FlowSummaryNode).getSummaryNode())
}

/**
 * Holds if data can flow from `node1` to `node2` via an assignment to `f`.
 * Thus, `node2` references an object with a field `f` that contains the
 * value of `node1`.
 *
 * The boolean `certain` is true if the destination address does not involve
 * any pointer arithmetic, and false otherwise. This has to do with whether a
 * store step can be used to clear a field (see `clearsContent`).
 */
predicate storeStepImpl(Node node1, Content c, Node node2, boolean certain) {
  exists(Stage2::Node n1, Stage2::Node n2 |
    node1 = TNode2(n1) and
    node2 = TNode2(n2) and
    Stage2::storeStep(n1, c, n2, certain)
  )
  or
  // models-as-data summarized flow
  FlowSummaryImpl::Private::Steps::summaryStoreStep(node1.(FlowSummaryNode).getSummaryNode(), c,
    node2.(FlowSummaryNode).getSummaryNode()) and
  certain = true
}

/**
 * Holds if data can flow from `node1` to `node2` via an assignment to `f`.
 * Thus, `node2` references an object with a field `f` that contains the
 * value of `node1`.
 */
predicate storeStep(Node node1, ContentSet c, Node node2) { storeStepImpl(node1, c, node2, _) }

// Needed to join on both an operand and an index at the same time.
pragma[noinline]
predicate nodeHasOperand(Node node, Operand operand, int indirectionIndex) {
  exists(Stage2::Node n |
    node = TNode2(n) and
    Stage2::nodeHasOperand(n, operand, indirectionIndex)
  )
}

// Needed to join on both an instruction and an index at the same time.
pragma[noinline]
predicate nodeHasInstruction(Node node, Instruction instr, int indirectionIndex) {
  exists(Stage2::Node n |
    node = TNode2(n) and
    Stage2::nodeHasInstruction(n, instr, indirectionIndex)
  )
}

/**
 * Holds if data can flow from `node1` to `node2` via a read of `f`.
 * Thus, `node1` references an object with a field `f` whose value ends up in
 * `node2`.
 */
predicate readStep(Node node1, ContentSet c, Node node2) {
  exists(Stage2::Node n1, Stage2::Node n2 |
    node1 = TNode2(n1) and
    node2 = TNode2(n2) and
    Stage2::readStep(n1, c, n2)
  )
  or
  // models-as-data summarized flow
  FlowSummaryImpl::Private::Steps::summaryReadStep(node1.(FlowSummaryNode).getSummaryNode(), c,
    node2.(FlowSummaryNode).getSummaryNode())
}

/**
 * Holds if values stored inside content `c` are cleared at node `n`.
 */
predicate clearsContent(Node n, ContentSet c) {
  n =
    any(PostUpdateNode pun, Content d | d.impliesClearOf(c) and storeStepImpl(_, d, pun, true) | pun)
        .getPreUpdateNode() and
  (
    // The crement operations and pointer addition and subtraction self-assign. We do not
    // want to clear the contents if it is indirectly pointed at by any of these operations,
    // as part of the contents might still be accessible afterwards. If there is no such
    // indirection clearing the contents is safe.
    not exists(Operand op, Cpp::Operation p |
      n.(IndirectOperandNode).hasOperandAndIndirectionIndex(op, _) and
      (
        p instanceof Cpp::AssignPointerAddExpr or
        p instanceof Cpp::AssignPointerSubExpr or
        p instanceof Cpp::CrementOperation
      )
    |
      p.getAnOperand() = op.getUse().getAst()
    )
    or
    forex(PostUpdateNode pun, Content d |
      pragma[only_bind_into](d).impliesClearOf(pragma[only_bind_into](c)) and
      storeStepImpl(_, d, pun, true) and
      pun.getPreUpdateNode() = n
    |
      c.(Content).getIndirectionIndex() = d.getIndirectionIndex()
    )
  )
}

/**
 * Holds if the value that is being tracked is expected to be stored inside content `c`
 * at node `n`.
 */
predicate expectsContent(Node n, ContentSet c) { none() }

predicate typeStrongerThan(DataFlowType t1, DataFlowType t2) { none() }

predicate localMustFlowStep(Node node1, Node node2) { none() }

/** Gets the type of `n` used for type pruning. */
DataFlowType getNodeType(Node n) {
  exists(n) and
  result instanceof VoidType // stub implementation
}

/**
 * Holds if `t1` and `t2` are compatible, that is, whether data can flow from
 * a node of type `t1` to a node of type `t2`.
 */
predicate compatibleTypes(DataFlowType t1, DataFlowType t2) {
  t1 instanceof VoidType and t2 instanceof VoidType // stub implementation
}

//////////////////////////////////////////////////////////////////////////////
// Java QL library compatibility wrappers
//////////////////////////////////////////////////////////////////////////////
/** A node that performs a type cast. */
class CastNode extends Node {
  CastNode() { none() } // stub implementation
}

private newtype TDataFlowCallable =
  TStage1Callable(Stage1::DataFlowCallable callable) {
    not callable instanceof FlowSummaryImpl::Public::SummarizedCallable
  } or
  TSummarizedCallable(FlowSummaryImpl::Public::SummarizedCallable c)

/**
 * A callable, which may be:
 *  - a function (that may contain code)
 *  - a summarized function (that may contain only `FlowSummaryNode`s)
 *  - a variable (this is used as context for global initialization, and also
 *    for the mid-point in interprocedural data flow between a write and read
 *    of a global variable in different functions).
 * When flow crosses from one _enclosing callable_ to another, the
 * interprocedural data-flow library discards call contexts and inserts a node
 * in the big-step relation used for human-readable path explanations.
 */
class DataFlowCallable extends TDataFlowCallable {
  /** Gets the location of this callable. */
  Location getLocation() { none() }

  /** Gets a textual representation of this callable. */
  string toString() { none() }

  /**
   * Gets the `Declaration` corresponding to this callable if it exists in the database.
   * For summarized callables (which may not exist in the database), use `asSummarizedCallable`.
   */
  Cpp::Declaration asSourceCallable() { this = TStage1Callable(result) }

  /**
   * Gets the underlying summarized callable, if
   * this callable is generated from a models-as-data
   * model.
   */
  FlowSummaryImpl::Public::SummarizedCallable asSummarizedCallable() {
    this = TSummarizedCallable(result)
  }

  /**
   * Gets the underlying `Declaration` of this `DataFlowCallable`. This
   * predicate returns a result for both source and summarized callables.
   */
  Cpp::Declaration getUnderlyingCallable() {
    result = this.asSummarizedCallable() or // SummarizedCallable = Function (in CPP)
    result = this.asSourceCallable()
  }
}

/**
 * A source callable, conceptually, a function in the source code for the
 * purpose of computing data flow. In practice this excludes functions that
 * are summarized using models-as-data (as we don't want to create
 * unmodeled flows or duplicate paths), and includes variables (for reasons
 * explained in `DataFlowCallable`).
 */
class SourceCallable extends DataFlowCallable, TStage1Callable {
  Cpp::Declaration decl;

  SourceCallable() { this = TStage1Callable(decl) }

  override string toString() { result = decl.toString() }

  override Location getLocation() { result = decl.getLocation() }
}

/**
 * A summarized callable, that is, a function synthesized from one or more
 * models-as-data models as a place to contain the corresponding
 * `FlowSummaryNode`s.
 */
class SummarizedCallable extends DataFlowCallable, TSummarizedCallable {
  FlowSummaryImpl::Public::SummarizedCallable sc;

  SummarizedCallable() { this = TSummarizedCallable(sc) }

  override string toString() { result = sc.toString() }

  override Location getLocation() { result = sc.getLocation() }
}

/** Gets the callable in which this node occurs. */
DataFlowCallable nodeGetEnclosingCallable(Node n) {
  result.getUnderlyingCallable() = n.getEnclosingCallable()
}

/** Holds if `p` is a `ParameterNode` of `c` with position `pos`. */
predicate isParameterNode(ParameterNode p, DataFlowCallable c, ParameterPosition pos) {
  p.isParameterOf(c, pos)
}

/** Holds if `arg` is an `ArgumentNode` of `c` with position `pos`. */
predicate isArgumentNode(ArgumentNode arg, DataFlowCall c, ArgumentPosition pos) {
  arg.argumentOf(c, pos)
}

private newtype TDataFlowCall =
  TNormalCall(Stage1::DataFlowCall call) or
  TSummaryCall(
    FlowSummaryImpl::Public::SummarizedCallable c, FlowSummaryImpl::Private::SummaryNode receiver
  ) {
    FlowSummaryImpl::Private::summaryCallbackRange(c, receiver)
  }

/**
 * A function call relevant for data flow. This includes calls from source
 * code and calls inside library callables with a flow summary.
 */
class DataFlowCall extends TDataFlowCall {
  /**
   * Gets the underlying data flow call instruction, if any.
   */
  CallInstruction asCallInstruction() { none() }

  /**
   * Gets the operand the specifies the target function of the call.
   */
  CallTargetOperand getCallTargetOperand() { none() }

  /**
   * Gets the `Function` that the call targets, if this is statically known.
   */
  DataFlowCallable getStaticCallTarget() { none() }

  /**
   * Gets the `index`'th argument operand. The qualifier is considered to have index `-1`.
   */
  ArgumentOperand getArgumentOperand(int index) { none() }

  /**
   * Gets the argument at the specified index, or `this` if `index` is `-1`.
   */
  pragma[noinline]
  final Instruction getArgument(int index) { result = this.getArgumentOperand(index).getDef() }

  /**
   * Gets the number of arguments of the call, including the `this` pointer, if any.
   */
  final int getNumberOfArguments() { result = count(this.getArgumentOperand(_)) }

  /**
   * Gets the enclosing callable, if any.
   */
  DataFlowCallable getEnclosingCallable() { none() }

  /**
   * Gets a textual representation of this call.
   */
  string toString() { none() }

  /**
   * Gets the location of this call.
   */
  Location getLocation() { none() }
}

/**
 * A function call relevant for data flow, that exists in source code.
 */
private class NormalCall extends DataFlowCall, TNormalCall {
  private Stage1::DataFlowCall call;

  NormalCall() { this = TNormalCall(call) }

  override CallInstruction asCallInstruction() { result = call }

  override CallTargetOperand getCallTargetOperand() { result = call.getCallTargetOperand() }

  override DataFlowCallable getStaticCallTarget() {
    result.getUnderlyingCallable() = call.getStaticCallTarget()
  }

  override ArgumentOperand getArgumentOperand(int index) { result = call.getArgumentOperand(index) }

  override DataFlowCallable getEnclosingCallable() {
    result.getUnderlyingCallable() = call.getEnclosingFunction()
  }

  override string toString() { result = call.toString() }

  override Location getLocation() { result = call.getLocation() }
}

/**
 * A synthesized call inside a callable with a flow summary.
 *
 * For example, consider the function:
 * ```
 * int myFunction(int (*funPtr)());
 * ```
 * with an accompanying models-as-data flow summary involving `funPtr` (for
 * example from `Argument[0].ReturnValue` to `ReturnValue`). A `SummaryCall`
 * will be synthesized representing a call to `funPtr` inside `myFunction`,
 * so that flow can be connected as described in the model.
 */
class SummaryCall extends DataFlowCall, TSummaryCall {
  private FlowSummaryImpl::Public::SummarizedCallable c;
  private FlowSummaryImpl::Private::SummaryNode receiver;

  SummaryCall() { this = TSummaryCall(c, receiver) }

  /**
   * Gets the data flow node that holds the address of the function this call
   * targets.
   */
  FlowSummaryImpl::Private::SummaryNode getReceiver() { result = receiver }

  // no implementation for `getCallTargetOperand()`, `getStaticCallTarget()`
  // or `getArgumentOperand(int index)`. This is because the flow summary
  // library is responsible for finding the call target, and there are no
  // IR nodes available for the call target operand or argument operands.
  override DataFlowCallable getEnclosingCallable() { result = TSummarizedCallable(c) }

  override string toString() { result = "[summary] call to " + receiver + " in " + c }

  override UnknownLocation getLocation() { any() }
}

module IsUnreachableInCall {
  private import semmle.code.cpp.ir.ValueNumbering
  private import semmle.code.cpp.controlflow.IRGuards as G

  private class ConstantIntegralTypeArgumentNode extends OperandNode instanceof ArgumentNode {
    int value;

    ConstantIntegralTypeArgumentNode() {
      node instanceof Stage2::ArgumentNode and
      value = op.getDef().(IntegerConstantInstruction).getValue().toInt()
    }

    int getValue() { result = value }
  }

  pragma[nomagic]
  private predicate ensuresEq(Operand left, Operand right, int k, IRBlock block, boolean areEqual) {
    any(G::IRGuardCondition guard).ensuresEq(left, right, k, block, areEqual)
  }

  pragma[nomagic]
  private predicate ensuresLt(Operand left, Operand right, int k, IRBlock block, boolean areEqual) {
    any(G::IRGuardCondition guard).ensuresLt(left, right, k, block, areEqual)
  }

  class NodeRegion instanceof IRBlock {
    string toString() { result = "NodeRegion" }

    predicate contains(Node n) { this = n.getBasicBlock() }
  }

  predicate isUnreachableInCall(NodeRegion block, DataFlowCall call) {
    exists(
      InstructionDirectParameterNode paramNode, ConstantIntegralTypeArgumentNode arg,
      IntegerConstantInstruction constant, int k, Operand left, Operand right, int argval
    |
      // arg flows into `paramNode`
      DataFlowImplCommon::viableParamArg(call, pragma[only_bind_into](paramNode),
        pragma[only_bind_into](arg)) and
      left = constant.getAUse() and
      right = valueNumber(paramNode.getInstruction()).getAUse() and
      argval = arg.getValue()
    |
      // and there's a guard condition which ensures that the result of `left == right + k` is `areEqual`
      exists(boolean areEqual | ensuresEq(left, right, k, block, areEqual) |
        // this block ensures that left = right + k, but it holds that `left != right + k`
        areEqual = true and
        constant.getValue().toInt() != argval + k
        or
        // this block ensures that or `left != right + k`, but it holds that `left = right + k`
        areEqual = false and
        constant.getValue().toInt() = argval + k
      )
      or
      // or there's a guard condition which ensures that the result of `left < right + k` is `isLessThan`
      exists(boolean isLessThan | ensuresLt(left, right, k, block, isLessThan) |
        isLessThan = true and
        // this block ensures that `left < right + k`, but it holds that `left >= right + k`
        constant.getValue().toInt() >= argval + k
        or
        // this block ensures that `left >= right + k`, but it holds that `left < right + k`
        isLessThan = false and
        constant.getValue().toInt() < argval + k
      )
    )
  }
}

import IsUnreachableInCall

/**
 * Holds if access paths with `c` at their head always should be tracked at high
 * precision. This disables adaptive access path precision for such access paths.
 */
predicate forceHighPrecision(Content c) { c instanceof ElementContent }

private class SsaPhiInputNode extends Node2 {
  override Stage2::SsaPhiInputNode node;
}

/** Holds if `n` should be hidden from path explanations. */
predicate nodeIsHidden(Node n) {
  n instanceof OperandNode and
  not n instanceof ArgumentNode and
  not n.asOperand() instanceof StoreValueOperand
  or
  n instanceof FinalGlobalValue
  or
  n instanceof InitialGlobalValue
  or
  n instanceof SsaPhiInputNode
}

predicate neverSkipInPathGraph(Node n) {
  // Always show the right-hand side of assignments in the path graph
  exists(n.asDefinition())
  or
  exists(n.asIndirectDefinition())
}

class LambdaCallKind = Unit;

/** Holds if `creation` is an expression that creates a lambda of kind `kind` for `c`. */
predicate lambdaCreation(Node creation, LambdaCallKind kind, DataFlowCallable c) {
  creation.asInstruction().(FunctionAddressInstruction).getFunctionSymbol() = c.asSourceCallable() and
  exists(kind)
}

/** Holds if `call` is a lambda call of kind `kind` where `receiver` is the lambda expression. */
predicate lambdaCall(DataFlowCall call, LambdaCallKind kind, Node receiver) {
  (
    call.(SummaryCall).getReceiver() = receiver.(FlowSummaryNode).getSummaryNode() or
    call.asCallInstruction().getCallTargetOperand() = receiver.asOperand()
  ) and
  exists(kind)
}

/** Extra data-flow steps needed for lambda flow analysis. */
predicate additionalLambdaFlowStep(Node nodeFrom, Node nodeTo, boolean preservesValue) { none() }

predicate knownSourceModel(Node source, string model) { External::sourceNode(source, _, model) }

predicate knownSinkModel(Node sink, string model) { External::sinkNode(sink, _, model) }

/**
 * Holds if flow is allowed to pass from parameter `p` and back to itself as a
 * side-effect, resulting in a summary from `p` to itself.
 *
 * One example would be to allow flow like `p.foo = p.bar;`, which is disallowed
 * by default as a heuristic.
 */
predicate allowParameterReturnInSelf(ParameterNode p) {
  p instanceof IndirectParameterNode
  or
  // models-as-data summarized flow
  exists(DataFlowCallable c, ParameterPosition pos |
    p.isParameterOf(c, pos) and
    FlowSummaryImpl::Private::summaryAllowParameterReturnInSelf(c.asSummarizedCallable(), pos)
  )
}

private predicate fieldHasApproxName(Field f, string s) {
  s = f.getName().charAt(0) and
  // Reads and writes of union fields are tracked using `UnionContent`.
  not f.getDeclaringType() instanceof Cpp::Union
}

private predicate unionHasApproxName(Cpp::Union u, string s) { s = u.getName().charAt(0) }

cached
private newtype TContentApprox =
  TFieldApproxContent(string s) { fieldHasApproxName(_, s) } or
  TUnionApproxContent(string s) { unionHasApproxName(_, s) } or
  TElementApproxContent()

/** An approximated `Content`. */
class ContentApprox extends TContentApprox {
  string toString() { none() } // overridden in subclasses
}

private class FieldApproxContent extends ContentApprox, TFieldApproxContent {
  string s;

  FieldApproxContent() { this = TFieldApproxContent(s) }

  Field getAField() { fieldHasApproxName(result, s) }

  string getPrefix() { result = s }

  final override string toString() { result = s }
}

private class UnionApproxContent extends ContentApprox, TUnionApproxContent {
  string s;

  UnionApproxContent() { this = TUnionApproxContent(s) }

  Cpp::Union getAUnion() { unionHasApproxName(result, s) }

  string getPrefix() { result = s }

  final override string toString() { result = s }
}

private class ElementApproxContent extends ContentApprox, TElementApproxContent {
  final override string toString() { result = "ElementApprox" }
}

/** Gets an approximated value for content `c`. */
pragma[inline]
ContentApprox getContentApprox(Content c) {
  exists(string prefix, Field f |
    prefix = result.(FieldApproxContent).getPrefix() and
    f = c.(FieldContent).getField() and
    fieldHasApproxName(f, prefix)
  )
  or
  exists(string prefix, Cpp::Union u |
    prefix = result.(UnionApproxContent).getPrefix() and
    u = c.(UnionContent).getUnion() and
    unionHasApproxName(u, prefix)
  )
  or
  c instanceof ElementContent and
  result instanceof ElementApproxContent
}

/**
 * A local flow relation that includes both local steps, read steps and
 * argument-to-return flow through summarized functions.
 */
private predicate localFlowStepWithSummaries(Node node1, Node node2) {
  localFlowStep(node1, node2)
  or
  readStep(node1, _, node2)
  or
  DataFlowImplCommon::argumentValueFlowsThrough(node1, _, node2, _)
}

/** Holds if `node` flows to a node that is used in a `SwitchInstruction`. */
private predicate localStepsToSwitch(Node node) {
  node.asOperand() = any(SwitchInstruction switch).getExpressionOperand()
  or
  exists(Node succ |
    localStepsToSwitch(succ) and
    localFlowStepWithSummaries(node, succ)
  )
}

/**
 * Holds if `node` is part of a path from a `ParameterNode` to an operand
 * of a `SwitchInstruction`.
 */
private predicate localStepsFromParameterToSwitch(Node node) {
  localStepsToSwitch(node) and
  (
    node instanceof ParameterNode
    or
    exists(Node prev |
      localStepsFromParameterToSwitch(prev) and
      localFlowStepWithSummaries(prev, node)
    )
  )
}

/**
 * The local flow relation `localFlowStepWithSummaries` pruned to only
 * include steps that are part of a path from a `ParameterNode` to an
 * operand of a `SwitchInstruction`.
 */
private predicate getAdditionalFlowIntoCallNodeTermStep(Node node1, Node node2) {
  localStepsFromParameterToSwitch(node1) and
  localStepsFromParameterToSwitch(node2) and
  localFlowStepWithSummaries(node1, node2)
}

/** Gets the `IRVariable` associated with the parameter node `p`. */
pragma[nomagic]
private IRVariable getIRVariableForParameterNode(ParameterNode p) {
  result = p.(InstructionDirectParameterNode).getIRVariable()
  or
  result.getAst() = p.(IndirectParameterNode).getParameter()
}

/** Holds if `v` is the source variable corresponding to the parameter represented by `p`. */
pragma[nomagic]
private predicate parameterNodeHasSourceVariable(ParameterNode p, Stage2::SourceVariable v) {
  v.getIRVariable() = getIRVariableForParameterNode(p) and
  exists(Stage1::Position pos | p.isParameterOf(_, pos) |
    pos.getIndirectionIndex() = 0 and
    v.getIndirection() = 1
    or
    pos.getIndirectionIndex() + 1 = v.getIndirection()
  )
}

private EdgeKind caseOrDefaultEdge() {
  result instanceof CaseEdge or
  result instanceof DefaultEdge
}

/**
 * Gets the number of switch branches that that read from (or write to) the parameter `p`.
 */
private int countNumberOfBranchesUsingParameter(SwitchInstruction switch, ParameterNode p) {
  exists(Stage2::SourceVariable sv |
    parameterNodeHasSourceVariable(p, sv) and
    // Count the number of cases that use the parameter. We do this by finding the phi node
    // that merges the uses/defs of the parameter. There might be multiple such phi nodes, so
    // we pick the one with the highest edge count.
    result =
      max(Stage2::SsaPhiNode phi |
        phi.hasIndexInBlock(switch.getSuccessor(caseOrDefaultEdge()).getBlock().dominanceFrontier(),
          _) and
        phi.getSourceVariable() = sv
      |
        strictcount(phi.getAnInput())
      )
  )
}

pragma[nomagic]
private predicate isInputOutput(
  DF::DataFlowFunction target, Node node1, Node node2, IO::FunctionInput input,
  IO::FunctionOutput output
) {
  exists(CallInstruction call |
    node1 = callInput(call, input) and
    node2 = callOutput(call, output) and
    call.getStaticCallTarget() = target and
    target.hasDataFlow(input, output)
  )
}

/**
 * Holds if the data-flow step from `node1` to `node2` can be used to
 * determine where side-effects may return from a callable.
 * For C/C++, this means that the step from `node1` to `node2` not only
 * preserves the value, but also preserves the identity of the value.
 * For example, the assignment to `x` that reads the value of `*p` in
 * ```cpp
 * int* p = ...
 * int x = *p;
 * ```
 * does not preserve the identity of `*p`.
 *
 * Similarly, a function that copies the contents of a string into a new location
 * does not also preserve the identity. For example, `strdup(p)` does not
 * preserve the identity of `*p` (since it allocates new storage and copies
 * the string into the new storage).
 */
bindingset[node1, node2]
pragma[inline_late]
predicate validParameterAliasStep(Node node1, Node node2) {
  // When flow-through summaries are computed we track which parameters flow to out-going parameters.
  // In an example such as:
  // ```
  // modify(int* px) { *px = source(); }
  // void modify_copy(int* p) {
  //   int x = *p;
  //   modify(&x);
  // }
  // ```
  // since dataflow tracks each indirection as a separate SSA variable dataflow
  // sees the above roughly as
  // ```
  // modify(int* px, int deref_px) { deref_px = source(); }
  // void modify_copy(int* p, int deref_p) {
  //   int x = deref_p;
  //   modify(&x, x);
  // }
  // ```
  // and when dataflow computes flow from a parameter to a post-update node to
  // conclude which parameters are "updated" by the call to `modify_copy` it
  // finds flow from `x [post update]` to `deref_p [post update]`.
  // To prevent this we exclude steps that don't preserve identity. We do this
  // by excluding flow from the right-hand side of `StoreInstruction`s to the
  // `StoreInstruction`. This is sufficient because, for flow-through summaries,
  // we're only interested in indirect parameters such as `deref_p` in the
  // exampe above (i.e., the parameters with a non-zero indirection index), and
  // if that ever flows to the right-hand side of a `StoreInstruction` then
  // there must have been a dereference to reduce its indirection index down to
  // 0.
  not exists(Operand operand |
    node1.asOperand() = operand and
    node2.asInstruction().(StoreInstruction).getSourceValueOperand() = operand
  ) and
  (
    // Either this is not a modeled flow.
    not isInputOutput(_, node1, node2, _, _)
    or
    exists(DF::DataFlowFunction target, IO::FunctionInput input, IO::FunctionOutput output |
      // Or it is a modeled flow and there's `*input` to `*output` flow
      isInputOutput(target, node1, node2, input.getIndirectionInput(), output.getIndirectionOutput()) and
      // and in that case there should also be `input` to `output` flow
      target.hasDataFlow(input, output)
    )
  )
}

private predicate isTopLevel(Cpp::Stmt s) { any(Function f).getBlock().getAStmt() = s }

private Cpp::Stmt getAChainedBranch(Cpp::IfStmt s) {
  result = s.getThen()
  or
  exists(Cpp::Stmt elseBranch | s.getElse() = elseBranch |
    result = getAChainedBranch(elseBranch)
    or
    result = elseBranch and not elseBranch instanceof Cpp::IfStmt
  )
}

private class SsaPhiNode extends Node2 {
  override Stage2::SsaPhiNode node;
}

private Instruction getAnInstruction(Node n) {
  result = n.asInstruction()
  or
  not n instanceof InstructionNode and
  result = n.asOperand().getUse()
  or
  result = n.(SsaPhiNode).getBasicBlock().getFirstInstruction()
  or
  result = n.(SsaPhiInputNode).getBasicBlock().getFirstInstruction()
  or
  n.(IndirectInstructionNode).hasInstructionAndIndirectionIndex(result, _)
  or
  not n instanceof IndirectInstructionNode and
  exists(Operand operand |
    n.(IndirectOperandNode).hasOperandAndIndirectionIndex(operand, _) and
    result = operand.getUse()
  )
  or
  result = getAnInstruction(n.(PostUpdateNode).getPreUpdateNode())
}

private newtype TDataFlowSecondLevelScope =
  TTopLevelIfBranch(Cpp::Stmt s) {
    exists(Cpp::IfStmt ifstmt | s = getAChainedBranch(ifstmt) and isTopLevel(ifstmt))
  } or
  TTopLevelSwitchCase(Cpp::SwitchCase s) {
    exists(Cpp::SwitchStmt switchstmt | s = switchstmt.getASwitchCase() and isTopLevel(switchstmt))
  }

/**
 * A second-level control-flow scope in a `switch` or a chained `if` statement.
 *
 * This is a `switch` case or a branch of a chained `if` statement, given that
 * the `switch` or `if` statement is top level, that is, it is not nested inside
 * other CFG constructs.
 */
class DataFlowSecondLevelScope extends TDataFlowSecondLevelScope {
  /** Gets a textual representation of this element. */
  string toString() {
    exists(Cpp::Stmt s | this = TTopLevelIfBranch(s) | result = s.toString())
    or
    exists(Cpp::SwitchCase s | this = TTopLevelSwitchCase(s) | result = s.toString())
  }

  /** Gets the primary location of this element. */
  Cpp::Location getLocation() {
    exists(Cpp::Stmt s | this = TTopLevelIfBranch(s) | result = s.getLocation())
    or
    exists(Cpp::SwitchCase s | this = TTopLevelSwitchCase(s) | result = s.getLocation())
  }

  /**
   * Gets a statement directly contained in this scope. For an `if` branch, this
   * is the branch itself, and for a `switch case`, this is one the statements
   * of that case branch.
   */
  private Cpp::Stmt getAStmt() {
    exists(Cpp::Stmt s | this = TTopLevelIfBranch(s) | result = s)
    or
    exists(Cpp::SwitchCase s | this = TTopLevelSwitchCase(s) | result = s.getAStmt())
  }

  /** Gets a data-flow node nested within this scope. */
  Node getANode() {
    getAnInstruction(result).getAst().(Cpp::ControlFlowNode).getEnclosingStmt().getParentStmt*() =
      this.getAStmt()
  }
}

/** Gets the second-level scope containing the node `n`, if any. */
DataFlowSecondLevelScope getSecondLevelScope(Node n) { result.getANode() = n }

/**
 * Module that defines flow through iterators.
 * For example,
 * ```cpp
 * auto it = v.begin();
 * *it = source();
 * ...
 * sink(v[0]);
 * ```
 */
module IteratorFlow {
  private import codeql.ssa.Ssa as SsaImpl
  private import semmle.code.cpp.models.interfaces.Iterator as Interface
  private import semmle.code.cpp.models.implementations.Iterator as Impl

  /**
   * A variable of some type that can produce an iterator.
   */
  class SourceVariable extends Stage2::SourceVariable {
    SourceVariable() {
      exists(Interface::GetIteratorFunction gets, Cpp::FunctionInput input, int i |
        input.isParameterDerefOrQualifierObject(i) and
        gets.getsIterator(input, _)
      |
        this.getType().stripType() = gets.getParameter(i).getType().stripType()
        or
        i = -1 and
        this.getType().stripType() = gets.getDeclaringType()
      )
    }
  }

  private module SsaInput implements SsaImpl::InputSig<Location> {
    import Stage2::Stage2::InputSigCommon

    class SourceVariable = IteratorFlow::SourceVariable;

    /** A call to function that dereferences an iterator. */
    private class IteratorPointerDereferenceCall extends CallInstruction {
      IteratorPointerDereferenceCall() {
        this.getStaticCallTarget() instanceof Impl::IteratorPointerDereferenceOperator
      }
    }

    /** A call to a function that obtains an iterator. */
    private class GetsIteratorCall extends CallInstruction {
      GetsIteratorCall() { this.getStaticCallTarget() instanceof Impl::GetIteratorFunction }
    }

    /** A call to `operator++` or `operator--` on an iterator. */
    private class IteratorCrementCall extends CallInstruction {
      IteratorCrementCall() { this.getStaticCallTarget() instanceof Impl::IteratorCrementOperator }
    }

    /**
     * Gets an ultimate definition of `def`.
     *
     * Note: Unlike `def.getAnUltimateDefinition()` this predicate also
     * traverses back through iterator increment and decrement operations.
     */
    private Stage2::Def getAnUltimateDefinition(Stage2::Def def) {
      result = def.getAnUltimateDefinition()
      or
      exists(IRBlock bb, int i, IteratorCrementCall crementCall, Stage2::SourceVariable sv |
        crementCall = def.getValue().asInstruction().(StoreInstruction).getSourceValue() and
        sv = def.getSourceVariable() and
        bb.getInstruction(i) = crementCall and
        Stage2::SsaCached::ssaDefReachesReadExt(sv, result.asDef(), bb, i)
      )
    }

    /**
     * Holds if `write` is an instruction that writes to address `address`
     */
    private predicate isIteratorWrite(Instruction write, Operand address) {
      exists(Stage2::DefImpl writeDef, IRBlock bb, int i |
        writeDef.hasIndexInBlock(bb, i, _) and
        bb.getInstruction(i) = write and
        address = writeDef.getAddressOperand()
      )
    }

    /**
     * Holds if `writeToDeref` is a write to an iterator that was obtained
     * by `beginCall`. That is, the following instruction sequence holds:
     * ```cpp
     * it = container.begin(); // or a similar iterator-obtaining function call
     * ...
     * *it = value;
     * ```
     */
    private predicate isIteratorStoreInstruction(
      GetsIteratorCall beginCall, Instruction writeToDeref
    ) {
      exists(
        StoreInstruction beginStore, IRBlock bbStar, int iStar, Stage2::Def def,
        IteratorPointerDereferenceCall starCall, Stage2::Def ultimate, Operand address
      |
        isIteratorWrite(writeToDeref, address) and
        exists(Stage0::OutNode out |
          out.getCall() = starCall and
          out.(Stage0::OperandNode).getOperand() = address
        ) and
        bbStar.getInstruction(iStar) = starCall and
        Stage2::SsaCached::ssaDefReachesReadExt(_, def.asDef(), bbStar, iStar) and
        ultimate = getAnUltimateDefinition*(def) and
        beginStore = ultimate.getValue().asInstruction() and
        exists(Stage0::OutNode out |
          out.getCall() = beginCall and
          out.(Stage0::OperandNode).getOperand() = beginStore.getSourceValueOperand()
        )
      )
    }

    /**
     * Holds if `(bb, i)` contains a write to an iterator that may have been obtained
     * by calling `begin` (or related functions) on the variable `v`.
     */
    predicate variableWrite(BasicBlock bb, int i, SourceVariable v, boolean certain) {
      certain = false and
      exists(GetsIteratorCall beginCall, Instruction writeToDeref, IRBlock bbQual, int iQual |
        isIteratorStoreInstruction(beginCall, writeToDeref) and
        bb.getInstruction(i) = writeToDeref and
        bbQual.getInstruction(iQual) = beginCall and
        Stage2::SsaCached::variableRead(bbQual, iQual, v, _)
      )
    }

    /** Holds if `(bb, i)` reads the container variable `v`. */
    predicate variableRead(BasicBlock bb, int i, SourceVariable v, boolean certain) {
      Stage2::SsaCached::variableRead(bb, i, v, certain)
    }
  }

  private module IteratorSsa = SsaImpl::Make<Location, SsaInput>;

  cached
  private newtype TSsaDef =
    TDef(IteratorSsa::DefinitionExt def) or
    TPhi(PhiNode phi)

  abstract private class SsaDef extends TSsaDef {
    /** Gets a textual representation of this element. */
    string toString() { none() }

    /** Gets the underlying non-phi definition or use. */
    IteratorSsa::DefinitionExt asDef() { none() }

    /** Gets the underlying phi node. */
    PhiNode asPhi() { none() }

    /** Gets the location of this element. */
    abstract Location getLocation();
  }

  private class Def extends TDef, SsaDef {
    IteratorSsa::DefinitionExt def;

    Def() { this = TDef(def) }

    final override IteratorSsa::DefinitionExt asDef() { result = def }

    final override Location getLocation() { result = this.getImpl().getLocation() }

    /** Gets the variable written to by this definition. */
    final SourceVariable getSourceVariable() { result = def.getSourceVariable() }

    override string toString() { result = def.toString() }

    /**
     * Holds if this definition (or use) has index `index` in block `block`,
     * and is a definition (or use) of the variable `sv`.
     */
    predicate hasIndexInBlock(IRBlock block, int index, SourceVariable sv) {
      def.definesAt(sv, block, index, _)
    }

    private Stage2::DefImpl getImpl() {
      exists(IRBlock bb, int i |
        this.hasIndexInBlock(bb, i, _) and
        result.hasIndexInBlock(bb, i)
      )
    }

    /** Gets the value written by this definition (i.e., the "right-hand side"). */
    Stage0::Node getValue() { result = this.getImpl().getValue() }

    /** Gets the indirection index of this definition. */
    int getIndirectionIndex() { result = this.getImpl().getIndirectionIndex() }
  }

  private class Phi extends TPhi, SsaDef {
    PhiNode phi;

    Phi() { this = TPhi(phi) }

    final override PhiNode asPhi() { result = phi }

    final override Location getLocation() { result = phi.getBasicBlock().getLocation() }

    override string toString() { result = phi.toString() }

    SsaIteratorNode getNode() { result.getIteratorFlowNode() = phi }
  }

  private class PhiNode extends IteratorSsa::DefinitionExt {
    PhiNode() {
      this instanceof IteratorSsa::PhiNode or
      this instanceof IteratorSsa::PhiReadNode
    }

    SsaIteratorNode getNode() { result.getIteratorFlowNode() = this }
  }

  cached
  private module IteratorSsaCached {
    cached
    predicate adjacentDefRead(IRBlock bb1, int i1, SourceVariable sv, IRBlock bb2, int i2) {
      IteratorSsa::adjacentDefReadExt(_, sv, bb1, i1, bb2, i2)
      or
      exists(PhiNode phi |
        IteratorSsa::lastRefRedefExt(_, sv, bb1, i1, phi) and
        phi.definesAt(sv, bb2, i2, _)
      )
    }

    cached
    Node getAPriorDefinition(IteratorSsa::DefinitionExt next) {
      exists(IRBlock bb, int i, SourceVariable sv, IteratorSsa::DefinitionExt def |
        IteratorSsa::lastRefRedefExt(pragma[only_bind_into](def), pragma[only_bind_into](sv),
          pragma[only_bind_into](bb), pragma[only_bind_into](i), next) and
        nodeToDefOrUse(result, sv, bb, i, _)
      )
    }
  }

  /** The set of nodes necessary for iterator flow. */
  class IteratorFlowNode instanceof PhiNode {
    /** Gets a textual representation of this node. */
    string toString() { result = super.toString() }

    /** Gets the type of this node. */
    DataFlowType getType() {
      exists(Stage2::SourceVariable sv |
        super.definesAt(sv, _, _, _) and
        result = sv.getType()
      )
    }

    /** Gets the `Declaration` that contains this block. */
    Declaration getFunction() { result = super.getBasicBlock().getEnclosingFunction() }

    /** Gets the locatino of this node. */
    Location getLocation() { result = super.getBasicBlock().getLocation() }
  }

  private import IteratorSsaCached

  private predicate defToNode(Node node, Def def, boolean uncertain) {
    (
      nodeHasOperand(node, def.getValue().asOperand(), def.getIndirectionIndex())
      or
      nodeHasInstruction(node, def.getValue().asInstruction(), def.getIndirectionIndex())
    ) and
    uncertain = false
  }

  private predicate nodeToDefOrUse(
    Node node, SourceVariable sv, IRBlock bb, int i, boolean uncertain
  ) {
    exists(Def def |
      def.hasIndexInBlock(bb, i, sv) and
      defToNode(node, def, uncertain)
    )
    or
    useToNode(bb, i, sv, node) and
    uncertain = false
  }

  private predicate useToNode(IRBlock bb, int i, SourceVariable sv, Node nodeTo) {
    exists(PhiNode phi |
      phi.definesAt(sv, bb, i, _) and
      nodeTo = phi.getNode()
    )
    or
    exists(Stage2::UseImpl use |
      use.hasIndexInBlock(bb, i, sv) and
      nodeTo = TNode2(use.getNode())
    )
  }

  /**
   * Holds if `nodeFrom` flows to `nodeTo` in a single step.
   */
  predicate localFlowStep(Node nodeFrom, Node nodeTo) {
    exists(
      Node nFrom, SourceVariable sv, IRBlock bb1, int i1, IRBlock bb2, int i2, boolean uncertain
    |
      adjacentDefRead(bb1, i1, sv, bb2, i2) and
      nodeToDefOrUse(nFrom, sv, bb1, i1, uncertain) and
      useToNode(bb2, i2, sv, nodeTo)
    |
      if uncertain = true
      then
        nodeFrom =
          [
            nFrom,
            getAPriorDefinition(any(IteratorSsa::DefinitionExt next | next.definesAt(sv, bb1, i1, _)))
          ]
      else nFrom = nodeFrom
    )
  }
}
