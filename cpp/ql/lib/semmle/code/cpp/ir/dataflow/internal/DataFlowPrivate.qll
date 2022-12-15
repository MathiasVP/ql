private import cpp as Cpp
private import DataFlowUtil
private import semmle.code.cpp.ir.IR
private import DataFlowDispatch
private import DataFlowImplConsistency
private import semmle.code.cpp.ir.internal.IRCppLanguage
private import SsaInternals as Ssa

private predicate conversionInstrStep(Instruction i, Instruction conv) {
  exists(Operand use |
    use = unique( | | getAUse(i)) and
    conversionFlow(use, conv, false)
  )
}

private predicate instrConversion(Instruction i, Instruction conv) {
  not Ssa::ignoreInstruction(conv) and
  (
    i = conv // we make this predicate reflexive so that `EquivInstruction` is onto
    or
    conversionInstrStep(i, conv)
  )
}

private module EquivInstructionImpl =
  QlBuiltins::EquivalenceRelation<Instruction, instrConversion/2>;

class EquivInstruction extends EquivInstructionImpl::EquivalenceClass {
  Instruction getAnInstruction() { this = EquivInstructionImpl::getEquivalenceClass(result) }

  Instruction getUnconvertedInstruction() {
    result = this.getAnInstruction() and
    not conversionInstrStep(_, result)
  }

  Instruction getConvertedInstruction() {
    result = this.getAnInstruction() and
    not conversionInstrStep(result, _)
  }

  string toString() { result = concat(this.getAnInstruction().getOpcode().toString(), ", ") }

  Cpp::Location getLocation() { result = this.getConvertedInstruction().getLocation() }

  Type getResultType() { result = this.getConvertedInstruction().getResultType() }

  predicate isGLValue() { this.getConvertedInstruction().isGLValue() }

  Cpp::Declaration getEnclosingFunction() {
    result = this.getConvertedInstruction().getEnclosingFunction()
  }
}

private predicate operandConversion(Operand op1, Operand op2) {
  not Ssa::ignoreOperand(op2) and
  (
    op1 = op2
    or
    conversionOperandStep(op1, op2)
  )
}

private predicate conversionOperandStep(Operand op1, Operand op2) {
  exists(Instruction instr |
    conversionInstrStep(_, instr) and
    instr = op1.getUse() and
    instr = op2.getDef()
  )
}

private module EquivOperandImpl = QlBuiltins::EquivalenceRelation<Operand, operandConversion/2>;

class EquivOperand extends EquivOperandImpl::EquivalenceClass {
  Operand getAnOperand() { this = EquivOperandImpl::getEquivalenceClass(result) }

  Operand getUnconvertedOperand() {
    result = this.getAnOperand() and
    not conversionOperandStep(_, result)
  }

  Operand getConvertedOperand() {
    result = this.getAnOperand() and
    not conversionOperandStep(result, _)
  }

  string toString() { result = concat(this.getAnOperand().toString(), ", ") }

  Cpp::Location getLocation() { result = this.getConvertedOperand().getLocation() }

  predicate isGLValue() { this.getConvertedOperand().isGLValue() }

  Type getType() { result = this.getConvertedOperand().getType() }

  CppType getLanguageType() { result = this.getConvertedOperand().getLanguageType() }

  Cpp::Declaration getEnclosingFunction() {
    result = this.getConvertedOperand().getDef().getEnclosingFunction()
  }
}

cached
private module Cached {
  cached
  newtype TIRDataFlowNode0 =
    TInstructionNode0(EquivInstruction i) {
      // We exclude `void`-typed instructions because they cannot contain data.
      // However, if the instruction is a glvalue, and their type is `void`, then the result
      // type of the instruction is really `void*`, and thus we still want to have a dataflow
      // node for it.
      (not i.getResultType() instanceof VoidType or i.isGLValue())
    } or
    TOperandNode0(EquivOperand op) { not Ssa::ignoreOperand(op.getAnOperand()) }
}

private import Cached

class Node0Impl extends TIRDataFlowNode0 {
  /**
   * INTERNAL: Do not use.
   */
  Declaration getEnclosingCallable() { none() } // overridden in subclasses

  /** Gets the function to which this node belongs, if any. */
  Declaration getFunction() { none() } // overridden in subclasses

  /**
   * Gets the type of this node.
   *
   * If `asInstruction().isGLValue()` holds, then the type of this node
   * should be thought of as "pointer to `getType()`".
   */
  DataFlowType getType() { none() } // overridden in subclasses

  Instruction asUnconvertedInstruction() {
    result = this.(InstructionNode0).getUnconvertedInstruction()
  }

  Instruction asConvertedInstruction() {
    result = this.(InstructionNode0).getConvertedInstruction()
  }

  EquivOperand asEquivOperand() {
    result.getUnconvertedOperand() = this.(OperandNode0).getUnconvertedOperand()
  }

  Operand asUnconvertedOperand() { result = this.(OperandNode0).getUnconvertedOperand() }

  Operand asConvertedOperand() { result = this.(OperandNode0).getConvertedOperand() }

  /** INTERNAL: Do not use. */
  Location getLocationImpl() {
    none() // overridden by subclasses
  }

  /** INTERNAL: Do not use. */
  string toStringImpl() {
    none() // overridden by subclasses
  }

  /** Gets the location of this node. */
  final Location getLocation() { result = this.getLocationImpl() }

  /** Gets a textual representation of this node. */
  final string toString() { result = this.toStringImpl() }
}

/**
 * An instruction, viewed as a node in a data flow graph.
 */
class InstructionNode0 extends Node0Impl, TInstructionNode0 {
  EquivInstruction instr;

  InstructionNode0() { this = TInstructionNode0(instr) }

  Instruction getUnconvertedInstruction() { result = instr.getUnconvertedInstruction() }

  Instruction getConvertedInstruction() { result = instr.getConvertedInstruction() }

  override Declaration getEnclosingCallable() { result = this.getFunction() }

  override Declaration getFunction() { result = instr.getEnclosingFunction() }

  override DataFlowType getType() { result = instr.getResultType() }

  final override Location getLocationImpl() { result = instr.getLocation() }

  override string toStringImpl() {
    // This predicate is overridden in subclasses. This default implementation
    // does not use `Instruction.toString` because that's expensive to compute.
    result = instr.toString()
  }
}

/**
 * An operand, viewed as a node in a data flow graph.
 */
class OperandNode0 extends Node0Impl, TOperandNode0 {
  EquivOperand op;

  OperandNode0() { this = TOperandNode0(op) }

  /** Gets the operand corresponding to this node. */
  Operand getAnOperand() { result = op.getAnOperand() }

  Operand getUnconvertedOperand() { result = op.getUnconvertedOperand() }

  Operand getConvertedOperand() { result = op.getConvertedOperand() }

  override Declaration getEnclosingCallable() { result = this.getFunction() }

  override Declaration getFunction() {
    result = op.getUnconvertedOperand().getUse().getEnclosingFunction()
  }

  override DataFlowType getType() { result = op.getType() }

  final override Location getLocationImpl() { result = op.getLocation() }

  override string toStringImpl() { result = op.toString() }
}

/**
 * INTERNAL: Do not use.
 *
 * A node that represents the indirect value of an operand in the IR
 * after `index` number of loads.
 *
 * Note: Unlike `RawIndirectOperand`, a value of type `IndirectOperand` may
 * be an `OperandNode`.
 */
class IndirectOperand extends Node {
  EquivOperand operand;
  int indirectionIndex;

  IndirectOperand() {
    this.(RawIndirectOperand).getUnconvertedOperand() = operand.getUnconvertedOperand() and
    this.(RawIndirectOperand).getIndirectionIndex() = indirectionIndex
    or
    this.(OperandNode).getUnconvertedOperand() =
      Ssa::getIRRepresentationOfIndirectOperand(operand, indirectionIndex).getUnconvertedOperand()
  }

  /** Gets the underlying operand. */
  Operand getUnconvertedOperand() { result = operand.getUnconvertedOperand() }

  Operand getConvertedOperand() { result = operand.getConvertedOperand() }

  /** Gets the underlying indirection index. */
  int getIndirectionIndex() { result = indirectionIndex }

  /**
   * Holds if this `IndirectOperand` is represented directly in the IR instead of
   * a `RawIndirectionOperand` with operand `op` and indirection index `index`.
   */
  predicate isIRRepresentationOf(EquivOperand op, int index) {
    this instanceof OperandNode and
    (
      op = operand and
      index = indirectionIndex
    )
  }
}

/**
 * INTERNAL: Do not use.
 *
 * A node that represents the indirect value of an instruction in the IR
 * after `index` number of loads.
 *
 * Note: Unlike `RawIndirectInstruction`, a value of type `IndirectInstruction` may
 * be an `InstructionNode`.
 */
class IndirectInstruction extends Node {
  EquivInstruction instr;
  int indirectionIndex;

  IndirectInstruction() {
    this.(RawIndirectInstruction).getUnconvertedInstruction() = instr.getUnconvertedInstruction() and
    this.(RawIndirectInstruction).getIndirectionIndex() = indirectionIndex
    or
    this.(InstructionNode).getUnconvertedInstruction() =
      Ssa::getIRRepresentationOfIndirectInstruction(instr, indirectionIndex)
          .getUnconvertedInstruction()
  }

  /** Gets the underlying instruction. */
  Instruction getUnconvertedInstruction() { result = instr.getUnconvertedInstruction() }

  /** Gets the underlying instruction. */
  Instruction getConvertedInstruction() { result = instr.getConvertedInstruction() }

  /** Gets the underlying indirection index. */
  int getIndirectionIndex() { result = indirectionIndex }

  /**
   * Holds if this `IndirectInstruction` is represented directly in the IR instead of
   * a `RawIndirectionInstruction` with instruction `i` and indirection index `index`.
   */
  predicate isIRRepresentationOf(EquivInstruction i, int index) {
    this instanceof InstructionNode and
    (
      i = instr and
      index = indirectionIndex
    )
  }
}

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
private class PrimaryArgumentNode extends ArgumentNode, OperandNode {
  ArgumentOperand argument;

  PrimaryArgumentNode() {
    argument = this.getConvertedOperand() and
    exists(CallInstruction call | argument = call.getAnArgumentOperand())
  }

  override predicate argumentOf(DataFlowCall call, ArgumentPosition pos) {
    argument = call.getArgumentOperand(pos.(DirectPosition).getIndex())
  }
}

private class SideEffectArgumentNode extends ArgumentNode, SideEffectOperandNode {
  override predicate argumentOf(DataFlowCall dfCall, ArgumentPosition pos) {
    this.getCallInstruction() = dfCall and
    pos.(IndirectionPosition).getArgumentIndex() = this.getArgumentIndex() and
    pos.(IndirectionPosition).getIndirectionIndex() = super.getIndirectionIndex()
  }
}

/** A parameter position represented by an integer. */
class ParameterPosition = Position;

/** An argument position represented by an integer. */
class ArgumentPosition = Position;

abstract class Position extends TPosition {
  abstract string toString();
}

class DirectPosition extends Position, TDirectPosition {
  int index;

  DirectPosition() { this = TDirectPosition(index) }

  override string toString() {
    index = -1 and
    result = "this"
    or
    index != -1 and
    result = index.toString()
  }

  int getIndex() { result = index }
}

class IndirectionPosition extends Position, TIndirectionPosition {
  int argumentIndex;
  int indirectionIndex;

  IndirectionPosition() { this = TIndirectionPosition(argumentIndex, indirectionIndex) }

  override string toString() {
    if argumentIndex = -1
    then if indirectionIndex > 0 then result = "this indirection" else result = "this"
    else
      if indirectionIndex > 0
      then result = argumentIndex.toString() + " indirection"
      else result = argumentIndex.toString()
  }

  int getArgumentIndex() { result = argumentIndex }

  int getIndirectionIndex() { result = indirectionIndex }
}

newtype TPosition =
  TDirectPosition(int index) { exists(any(CallInstruction c).getArgument(index)) } or
  TIndirectionPosition(int argumentIndex, int indirectionIndex) {
    hasOperandAndIndex(_,
      any(EquivOperand equiv |
        equiv.getConvertedOperand() = any(CallInstruction call).getArgumentOperand(argumentIndex)
      ), indirectionIndex)
  }

private newtype TReturnKind =
  TNormalReturnKind(int index) {
    exists(IndirectReturnNode return |
      return.getConvertedAddressOperand() = any(ReturnValueInstruction r).getReturnAddressOperand() and
      index = return.getIndirectionIndex() - 1 // We subtract one because the return loads the value.
    )
  } or
  TIndirectReturnKind(int argumentIndex, int indirectionIndex) {
    exists(IndirectReturnNode return, ReturnIndirectionInstruction returnInd |
      returnInd.hasIndex(argumentIndex) and
      return.getConvertedAddressOperand() = returnInd.getSourceAddressOperand() and
      indirectionIndex = return.getIndirectionIndex()
    )
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
  int index;

  NormalReturnKind() { this = TNormalReturnKind(index) }

  override string toString() { result = "indirect return" }
}

private class IndirectReturnKind extends ReturnKind, TIndirectReturnKind {
  int argumentIndex;
  int indirectionIndex;

  IndirectReturnKind() { this = TIndirectReturnKind(argumentIndex, indirectionIndex) }

  override string toString() { result = "indirect outparam[" + argumentIndex.toString() + "]" }
}

/** A data flow node that occurs as the result of a `ReturnStmt`. */
class ReturnNode extends Node instanceof IndirectReturnNode {
  /** Gets the kind of this returned value. */
  abstract ReturnKind getKind();
}

/**
 * This predicate represents an annoying hack that we have to do. We use the
 * `ReturnIndirectionInstruction` to determine which variables need flow back
 * out of a function. However, the IR will unconditionally create those for a
 * variable passed to a function even though the variable was never updated by
 * the function. And if a function has too many `ReturnNode`s the dataflow
 * library lowers its precision for that function by disabling field flow.
 *
 * So we those eliminate `ReturnNode`s that would have otherwise been created
 * by this unconditional `ReturnIndirectionInstruction` by requiring that there
 * must exist an SSA definition of the IR variable in the function.
 */
private predicate hasNonInitializeParameterDef(IRVariable v) {
  exists(Ssa::Def def |
    not def.getValue().asUnconvertedInstruction() instanceof InitializeParameterInstruction and
    v = def.getSourceVariable().getBaseVariable().(Ssa::BaseIRVariable).getIRVariable()
  )
}

class ReturnIndirectionNode extends IndirectReturnNode, ReturnNode {
  override ReturnKind getKind() {
    exists(EquivOperand op, int i |
      hasOperandAndIndex(this, pragma[only_bind_into](op), pragma[only_bind_into](i))
    |
      exists(int argumentIndex, ReturnIndirectionInstruction returnInd |
        op.getConvertedOperand() = returnInd.getSourceAddressOperand() and
        returnInd.hasIndex(argumentIndex) and
        hasNonInitializeParameterDef(returnInd.getIRVariable()) and
        result = TIndirectReturnKind(argumentIndex, pragma[only_bind_into](i))
      )
      or
      exists(ReturnValueInstruction return |
        op.getConvertedOperand() = return.getReturnAddressOperand() and
        result = TNormalReturnKind(i - 1)
      )
    )
  }
}

private Operand fullyConvertedCallStep(Operand op) {
  not exists(getANonConversionUse(op)) and
  exists(Instruction instr |
    conversionFlow(op, instr, _) and
    result = getAUse(instr)
  )
}

/**
 * Gets the instruction that uses this operand, if the instruction is not
 * ignored for dataflow purposes.
 */
private Instruction getUse(Operand op) {
  result = op.getUse() and
  not Ssa::ignoreOperand(op)
}

/** Gets a use of the instruction `instr` that is not ignored for dataflow purposes. */
Operand getAUse(Instruction instr) {
  result = instr.getAUse() and
  not Ssa::ignoreOperand(result)
}

/**
 * Gets a use of `operand` that is:
 * - not ignored for dataflow purposes, and
 * - not a conversion-like instruction.
 */
private Instruction getANonConversionUse(Operand operand) {
  result = getUse(operand) and
  not conversionFlow(_, result, _)
}

/**
 * Gets the operand that represents the first use of the value of `call` following
 * a sequence of conversion-like instructions.
 */
predicate operandForfullyConvertedCall(Operand operand, CallInstruction call) {
  exists(getANonConversionUse(operand)) and
  (
    operand = getAUse(call)
    or
    operand = fullyConvertedCallStep*(getAUse(call))
  )
}

/**
 * Gets the instruction that represents the first use of the value of `call` following
 * a sequence of conversion-like instructions.
 *
 * This predicate only holds if there is no suitable operand (i.e., no operand of a non-
 * conversion instruction) to use to represent the value of `call` after conversions.
 */
predicate instructionForfullyConvertedCall(Instruction instr, CallInstruction call) {
  not operandForfullyConvertedCall(_, call) and
  (
    // If there is no use of the call then we pick the call instruction
    not exists(getAUse(call)) and
    instr = call
    or
    // Otherwise, flow to the first non-conversion use.
    exists(Operand operand | operand = fullyConvertedCallStep*(getAUse(call)) |
      instr = getANonConversionUse(operand)
    )
  )
}

/** Holds if `node` represents the output node for `call`. */
private predicate simpleOutNode(Node node, CallInstruction call) {
  // TODO: Does this predicate map a call to multiple nodes?
  node.asUnconvertedOperand().getDef() = call
  or
  node.asUnconvertedInstruction() = call
}

/** A data flow node that represents the output of a call. */
class OutNode extends Node {
  OutNode() {
    // Return values not hidden behind indirections
    simpleOutNode(this, _)
    or
    // Return values hidden behind indirections
    this instanceof IndirectReturnOutNode
    or
    // Modified arguments hidden behind indirections
    this instanceof IndirectArgumentOutNode
  }

  /** Gets the underlying call. */
  abstract DataFlowCall getCall();

  abstract ReturnKind getReturnKind();
}

private class DirectCallOutNode extends OutNode {
  CallInstruction call;

  DirectCallOutNode() { simpleOutNode(this, call) }

  override DataFlowCall getCall() { result = call }

  override ReturnKind getReturnKind() { result = TNormalReturnKind(0) }
}

private class IndirectCallOutNode extends OutNode, IndirectReturnOutNode {
  override DataFlowCall getCall() { result = this.getCallInstruction() }

  override ReturnKind getReturnKind() { result = TNormalReturnKind(this.getIndirectionIndex()) }
}

private class SideEffectOutNode extends OutNode, IndirectArgumentOutNode {
  override DataFlowCall getCall() { result = this.getCallInstruction() }

  override ReturnKind getReturnKind() {
    result = TIndirectReturnKind(this.getArgumentIndex(), this.getIndirectionIndex())
  }
}

/**
 * Gets a node that can read the value returned from `call` with return kind
 * `kind`.
 */
OutNode getAnOutNode(DataFlowCall call, ReturnKind kind) {
  result.getCall() = call and
  result.getReturnKind() = kind
}

/**
 * Holds if data can flow from `node1` to `node2` in a way that loses the
 * calling context. For example, this would happen with flow through a
 * global or static variable.
 */
predicate jumpStep(Node n1, Node n2) {
  exists(Cpp::GlobalOrNamespaceVariable v |
    v =
      n1.asUnconvertedInstruction()
          .(StoreInstruction)
          .getResultAddress()
          .(VariableAddressInstruction)
          .getAstVariable() and
    v = n2.asVariable()
    or
    v =
      n2.asUnconvertedInstruction()
          .(LoadInstruction)
          .getSourceAddress()
          .(VariableAddressInstruction)
          .getAstVariable() and
    v = n1.asVariable()
  )
}

/**
 * Holds if data can flow from `node1` to `node2` via an assignment to `f`.
 * Thus, `node2` references an object with a field `f` that contains the
 * value of `node1`.
 */
predicate storeStep(Node node1, Content c, PostFieldUpdateNode node2) {
  exists(int indirectionIndex1, int numberOfLoads, StoreInstruction store |
    nodeHasInstruction(node1,
      any(EquivInstruction equiv | equiv.getUnconvertedInstruction() = store),
      pragma[only_bind_into](indirectionIndex1)) and
    node2.getIndirectionIndex() = 1 and
    numberOfLoadsFromOperand(node2.getFieldAddress().getConvertedOperand(),
      any(EquivOperand equiv | equiv.getConvertedOperand() = store.getDestinationAddressOperand()),
      numberOfLoads)
  |
    exists(FieldContent fc | fc = c |
      fc.getField() = node2.getUpdatedField() and
      fc.getIndirectionIndex() = 1 + indirectionIndex1 + numberOfLoads
    )
    or
    exists(UnionContent uc | uc = c |
      uc.getAField() = node2.getUpdatedField() and
      uc.getIndirectionIndex() = 1 + indirectionIndex1 + numberOfLoads
    )
  )
}

/**
 * Holds if `operandFrom` flows to `operandTo` using a sequence of conversion-like
 * operations and exactly `n` `LoadInstruction` operations.
 */
private predicate numberOfLoadsFromOperandRec(Operand operandFrom, EquivOperand operandTo, int ind) {
  exists(Instruction load | Ssa::isDereference(load, operandFrom) |
    operandTo.getAnOperand() = operandFrom and ind = 0
    or
    numberOfLoadsFromOperand(load.getAUse(), operandTo, ind - 1)
  )
  or
  exists(Operand op, Instruction instr |
    instr = op.getDef() and
    conversionFlow(operandFrom, instr, _) and
    numberOfLoadsFromOperand(op, operandTo, ind)
  )
}

/**
 * Holds if `operandFrom` flows to `operandTo` using a sequence of conversion-like
 * operations and exactly `n` `LoadInstruction` operations.
 */
private predicate numberOfLoadsFromOperand(Operand operandFrom, EquivOperand operandTo, int n) {
  numberOfLoadsFromOperandRec(operandFrom, operandTo, n)
  or
  not Ssa::isDereference(_, operandFrom) and
  not conversionFlow(operandFrom, _, _) and
  operandFrom = operandTo.getAnOperand() and
  n = 0
}

// Needed to join on both an operand and an index at the same time.
pragma[noinline]
predicate nodeHasOperand(Node node, EquivOperand operand, int indirectionIndex) {
  node.asUnconvertedOperand() = operand.getUnconvertedOperand() and indirectionIndex = 0
  or
  hasOperandAndIndex(node, operand, indirectionIndex)
}

// Needed to join on both an instruction and an index at the same time.
pragma[noinline]
predicate nodeHasInstruction(Node node, EquivInstruction instr, int indirectionIndex) {
  node.asUnconvertedInstruction() = instr.getUnconvertedInstruction() and indirectionIndex = 0
  or
  hasInstructionAndIndex(node, instr, indirectionIndex)
}

/**
 * Holds if data can flow from `node1` to `node2` via a read of `f`.
 * Thus, `node1` references an object with a field `f` whose value ends up in
 * `node2`.
 */
predicate readStep(Node node1, Content c, Node node2) {
  exists(FieldAddress fa1, EquivOperand operand, int numberOfLoads, int indirectionIndex2 |
    nodeHasOperand(node2, operand, indirectionIndex2) and
    // The `1` here matches the `node2.getIndirectionIndex() = 1` conjunct
    // in `storeStep`.
    nodeHasOperand(node1, fa1.getObjectAddressOperand(), 1) and
    numberOfLoadsFromOperand(fa1.getConvertedOperand(), operand, numberOfLoads)
  |
    exists(FieldContent fc | fc = c |
      fc.getField() = fa1.getField() and
      fc.getIndirectionIndex() = indirectionIndex2 + numberOfLoads
    )
    or
    exists(UnionContent uc | uc = c |
      uc.getAField() = fa1.getField() and
      uc.getIndirectionIndex() = indirectionIndex2 + numberOfLoads
    )
  )
}

/**
 * Holds if values stored inside content `c` are cleared at node `n`.
 */
predicate clearsContent(Node n, Content c) {
  none() // stub implementation
}

/**
 * Holds if the value that is being tracked is expected to be stored inside content `c`
 * at node `n`.
 */
predicate expectsContent(Node n, ContentSet c) { none() }

/** Gets the type of `n` used for type pruning. */
DataFlowType getNodeType(Node n) {
  suppressUnusedNode(n) and
  result instanceof VoidType // stub implementation
}

/** Gets a string representation of a type returned by `getNodeType`. */
string ppReprType(DataFlowType t) { none() } // stub implementation

/**
 * Holds if `t1` and `t2` are compatible, that is, whether data can flow from
 * a node of type `t1` to a node of type `t2`.
 */
pragma[inline]
predicate compatibleTypes(DataFlowType t1, DataFlowType t2) {
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
class DataFlowCallable = Cpp::Declaration;

class DataFlowExpr = Expr;

class DataFlowType = Type;

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

module TestStep {
  private import DataFlowImplCommon as DataFlowImplCommon

  private predicate into(ArgumentNode node1, ParameterNode node2) {
    exists(CallInstruction call, ParameterPosition pos |
      node1.argumentOf(call, pos) and
      node2.isParameterOf(call.getStaticCallTarget(), pos)
    )
  }

  private predicate outOf(
    DataFlowImplCommon::ReturnNodeExt node1, DataFlowImplCommon::OutNodeExt node2, string msg
  ) {
    exists(DataFlowImplCommon::ReturnKindExt kind |
      node1.getKind() = kind and
      kind.getAnOutNode(any(CallInstruction call |
          call.getStaticCallTarget() = node1.getEnclosingCallable()
        )) = node2 and
      msg = kind.toString()
    )
  }

  private predicate argumentValueFlowsThrough(ArgumentNode n2, Content c, OutNode n1) {
    exists(Node mid1, ParameterNode p, ReturnNode r, Node mid2 |
      into(n2, p) and
      simpleLocalFlowStep*(p, mid2) and
      readStep(mid2, c, mid1) and
      simpleLocalFlowStep*(mid1, r) and
      outOf(r, n1, _)
    )
  }

  private predicate argumentValueFlowsThrough(ArgumentNode n2, OutNode n1) {
    exists(ParameterNode p, ReturnNode r |
      into(n2, p) and
      simpleLocalFlowStep*(p, r) and
      outOf(r, n1, _)
    )
  }

  private predicate reverseStepThroughInputOutputAlias(
    PostUpdateNode fromNode, PostUpdateNode toNode
  ) {
    exists(Node fromPre, Node toPre |
      fromPre = fromNode.getPreUpdateNode() and
      toPre = toNode.getPreUpdateNode()
    |
      exists(DataFlowCall c |
        fromPre = getAnOutNode(c, _) and
        toPre.(ArgumentNode).argumentOf(c, _) and
        simpleLocalFlowStep(toPre.(ArgumentNode), fromPre)
      )
      or
      argumentValueFlowsThrough(toPre, fromPre)
    )
  }

  predicate step(Node node1, Node node2, string msg) {
    stepFwd(_, node1) and
    not isBarrier(node1) and
    not isBarrier(node2) and
    (
      simpleLocalFlowStep(node1, node2) and msg = concat(node2.getAQlClass(), ", ")
      or
      reverseStepThroughInputOutputAlias(node1, node2) and msg = "reverse step through alias"
      or
      exists(Content c, string after | after = c.toString() |
        readStep(node1, c, node2) and msg = "Read " + after
        or
        storeStep(node1, c, node2) and msg = "Store " + after
        or
        exists(Node n1, Node n2 |
          n1 = node1.(PostUpdateNode).getPreUpdateNode() and
          n2 = node2.(PostUpdateNode).getPreUpdateNode() and
          readStep(n2, c, n1) and
          msg = "Reverse read " + c
        )
        or
        exists(OutNode n1, ArgumentNode n2 |
          n2 = node2.(PostUpdateNode).getPreUpdateNode() and
          n1 = node1.(PostUpdateNode).getPreUpdateNode() and
          argumentValueFlowsThrough(n2, c, n1) and
          msg = "Through " + after
        )
      )
      or
      into(node1, node2) and msg = "into"
      or
      outOf(node1, node2, msg)
    )
  }

  private predicate isBarrier(Node node) {
    node.asExpr().(Cpp::VariableAccess).getTarget().hasName("barrier")
  }

  predicate isSource(Node source) {
    // exists(Cpp::FunctionCall fc |
    //   fc.getTarget().hasName("source") and
    //   source.asExpr() = fc
    // )
    source.asUnconvertedInstruction().getResultId() = "r23_2"
  }

  private predicate stepFwd(Node node1, Node node2) {
    node1 = node2 and
    isSource(node1)
    or
    exists(Node mid |
      stepFwd(node1, mid) and
      step(mid, node2, _)
    )
  }
}
