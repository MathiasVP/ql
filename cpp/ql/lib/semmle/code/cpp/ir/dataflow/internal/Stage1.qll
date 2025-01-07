private import cpp
private import Base
private import semmle.code.cpp.ir.IR
private import StageSig
private import Stage0
private import codeql.dataflow.internal.AccessPathSyntax as AccessPath

module Stage1 implements StageSig {
  private newtype TNode =
    TNode0(Stage0::Node n) or
    TRawIndirectOperandNode(Stage0::Node node, int indirectionIndex) {
      Stage0Output::hasRawIndirectOperand(node.asOperand(), indirectionIndex)
    } or
    TRawIndirectInstructionNode(Stage0::Node node, int indirectionIndex) {
      not exists(node.asOperand()) and
      Stage0Output::hasRawIndirectInstruction(node.asInstruction(), indirectionIndex)
    } or
    TBodyLessParameterNode(Stage0::ParameterNode p, int indirectionIndex) {
      p.isBodyless() and
      indirectionIndex = [1 .. Stage0Output::getMaxIndirectionsForType(p.getType()) - 1] // indirectionIndex = 0 is already a TNode0
    }

  abstract private class NodeImpl extends TNode {
    /** Gets the instruction corresponding to this node, if any. */
    final Instruction asInstruction() { result = this.(InstructionNode).getInstruction() }

    /** Gets the operands corresponding to this node, if any. */
    final Operand asOperand() { result = this.(OperandNode).getOperand() }

    abstract string toString();

    abstract Declaration getEnclosingCallable();

    abstract Declaration getFunction();

    abstract DataFlowType getType();

    abstract Location getLocation();

    abstract predicate isGLValue();

    abstract string stars();

    predicate hasIndexInBlock(IRBlock block, int i) {
      exists(Stage0::Node n |
        this = TNode0(n)
        or
        this = TRawIndirectOperandNode(n, _)
        or
        this = TRawIndirectInstructionNode(n, _)
      |
        n.hasIndexInBlock(block, i)
      )
    }
  }

  final class Node = NodeImpl;

  additional Node inject(Stage0::Node n) { result = TNode0(n) }

  private class Node0 extends NodeImpl, TNode0 {
    Stage0::Node n;

    Node0() { this = TNode0(n) }

    override string toString() { result = n.toString() }

    final override Declaration getEnclosingCallable() { result = n.getEnclosingCallable() }

    final override Declaration getFunction() { result = n.getFunction() }

    final override DataFlowType getType() { result = n.getType() }

    final override Location getLocation() { result = n.getLocation() }

    final override predicate isGLValue() { n.isGLValue() }

    final override string stars() { result = n.stars() }
  }

  class OperandNode extends Node0 {
    override Stage0::OperandNode n;

    Operand getOperand() { result = n.getOperand() }
  }

  OperandNode operandNode(Operand operand) { result.getOperand() = operand }

  class InstructionNode extends Node0 {
    override Stage0::InstructionNode n;

    Instruction getInstruction() { result = n.getInstruction() }
  }

  InstructionNode instructionNode(Instruction instr) { result.getInstruction() = instr }

  /**
   * Indirect operand nodes that are represented by TRawIndirectOperandNode.
   */
  private class RawIndirectOperandNode0 extends NodeImpl, TRawIndirectOperandNode {
    Stage0::Node node;
    int indirectionIndex;

    RawIndirectOperandNode0() { this = TRawIndirectOperandNode(node, indirectionIndex) }

    /** Gets the underlying instruction. */
    final Operand getOperand() { result = node.asOperand() }

    /** Gets the underlying indirection index. */
    final int getIndirectionIndex() { result = indirectionIndex }

    override Declaration getFunction() {
      result = this.getOperand().getDef().getEnclosingFunction()
    }

    override Declaration getEnclosingCallable() { result = this.getFunction() }

    override predicate isGLValue() { this.getOperand().isGLValue() }

    override DataFlowType getType() {
      exists(int sub, DataFlowType type, boolean isGLValue |
        type = getOperandType(this.getOperand(), isGLValue) and
        if isGLValue = true then sub = 1 else sub = 0
      |
        result = Stage0Output::getTypeImpl(type.getUnderlyingType(), indirectionIndex - sub)
      )
    }

    final override Location getLocation() {
      if exists(this.getOperand().getLocation())
      then result = this.getOperand().getLocation()
      else result instanceof UnknownDefaultLocation
    }

    override string toString() { result = this.stars() + node.toString() }

    final override string stars() { result = repeatStars(indirectionIndex) }
  }

  /**
   * INTERNAL: Do not use.
   *
   * A node that represents the indirect value of an instruction in the IR
   * after `index` number of loads.
   */
  private class RawIndirectInstructionNode0 extends NodeImpl, TRawIndirectInstructionNode {
    Stage0::Node node;
    int indirectionIndex;

    RawIndirectInstructionNode0() { this = TRawIndirectInstructionNode(node, indirectionIndex) }

    /** Gets the underlying instruction. */
    final Instruction getInstruction() { result = node.asInstruction() }

    /** Gets the underlying indirection index. */
    final int getIndirectionIndex() { result = indirectionIndex }

    override Declaration getFunction() { result = this.getInstruction().getEnclosingFunction() }

    override Declaration getEnclosingCallable() { result = this.getFunction() }

    override predicate isGLValue() { this.getInstruction().isGLValue() }

    override DataFlowType getType() {
      exists(int sub, DataFlowType type, boolean isGLValue |
        type = getInstructionType(this.getInstruction(), isGLValue) and
        if isGLValue = true then sub = 1 else sub = 0
      |
        result = Stage0Output::getTypeImpl(type.getUnderlyingType(), indirectionIndex - sub)
      )
    }

    final override Location getLocation() {
      if exists(this.getInstruction().getLocation())
      then result = this.getInstruction().getLocation()
      else result instanceof UnknownDefaultLocation
    }

    override string toString() { result = this.stars() + node.toString() }

    final override string stars() { result = repeatStars(indirectionIndex) }
  }

  private class RawIndirectOperandNode extends Node {
    int indirectionIndex;
    Operand operand;

    RawIndirectOperandNode() {
      exists(Stage0::Node node | operand = node.asOperand() |
        this = TRawIndirectOperandNode(node, indirectionIndex)
        or
        this = TRawIndirectInstructionNode(node, indirectionIndex)
      )
    }

    Operand getOperand() { result = operand }

    int getIndirectionIndex() { result = indirectionIndex }
  }

  private class RawIndirectInstructionNode extends Node {
    int indirectionIndex;
    Instruction instr;

    RawIndirectInstructionNode() {
      exists(Stage0::Node node | instr = node.asInstruction() |
        this = TRawIndirectOperandNode(node, indirectionIndex)
        or
        this = TRawIndirectInstructionNode(node, indirectionIndex)
      )
    }

    Instruction getInstruction() { result = instr }

    int getIndirectionIndex() { result = indirectionIndex }
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
  class IndirectOperandNode extends Node {
    Operand operand;
    int indirectionIndex;

    IndirectOperandNode() {
      this.(RawIndirectOperandNode).getOperand() = operand and
      this.(RawIndirectOperandNode).getIndirectionIndex() = indirectionIndex
      or
      exists(Operand repr, int indirectionIndexRepr |
        Stage0Output::hasIRRepresentationOfIndirectOperand(operand, indirectionIndex, repr,
          indirectionIndexRepr) and
        nodeHasOperand(this, repr, indirectionIndexRepr)
      )
    }

    /** Gets the underlying operand and the underlying indirection index. */
    predicate hasOperandAndIndirectionIndex(Operand operand_, int indirectionIndex_) {
      operand_ = operand and
      indirectionIndex_ = indirectionIndex
    }
  }

  predicate hasOperandAndIndex(IndirectOperandNode n, Operand op, int indirectionIndex) {
    n.hasOperandAndIndirectionIndex(op, indirectionIndex)
  }

  predicate hasInstructionAndIndex(
    IndirectInstructionNode n, Instruction instr, int indirectionIndex
  ) {
    n.hasInstructionAndIndirectionIndex(instr, indirectionIndex)
  }

  predicate nodeHasOperand(Node node, Operand operand, int indirectionIndex) {
    node.asOperand() = operand and indirectionIndex = 0
    or
    hasOperandAndIndex(node, operand, indirectionIndex)
  }

  predicate nodeHasInstruction(Node node, Instruction instr, int indirectionIndex) {
    node.asInstruction() = instr and indirectionIndex = 0
    or
    hasInstructionAndIndex(node, instr, indirectionIndex)
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
  class IndirectInstructionNode extends Node {
    Instruction instr;
    int indirectionIndex;

    IndirectInstructionNode() {
      this.(RawIndirectInstructionNode).getInstruction() = instr and
      this.(RawIndirectInstructionNode).getIndirectionIndex() = indirectionIndex
      or
      exists(Instruction repr, int indirectionIndexRepr |
        Stage0Output::hasIRRepresentationOfIndirectInstruction(instr, indirectionIndex, repr,
          indirectionIndexRepr) and
        nodeHasInstruction(this, repr, indirectionIndexRepr)
      )
    }

    predicate hasInstructionAndIndirectionIndex(Instruction instr_, int indirectionIndex_) {
      instr = instr_ and
      indirectionIndex = indirectionIndex_
    }
  }

  class VariableNode extends Node0 {
    override Stage0::VariableNode n;

    Variable getVariable() { result = n.getVariable() }
  }

  private predicate simpleOperandLocalFlowStep(Instruction instr, Operand operand) {
    exists(Stage0::Node nInstr, Stage0::Node nOperand |
      nInstr.asInstruction() = instr and
      nOperand.asOperand() = operand
    |
      Stage0::localFlowStep(nInstr, nOperand)
      or
      // It may be that the same `Stage0::Node` represents both the
      // instruction and the operand. When that happens there is no local flow
      // step. However, we still want to represent that there's flow from the
      // instruction to the operand.
      nInstr = nOperand
    )
  }

  private predicate simpleInstructionLocalFlowStep(Operand operand, Instruction instr) {
    exists(Stage0::Node nInstr, Stage0::Node nOperand |
      nInstr.asInstruction() = instr and
      nOperand.asOperand() = operand
    |
      Stage0::localFlowStep(nOperand, nInstr)
      or
      // It may be that the same `Stage0::Node` represents both the
      // instruction and the operand. When that happens there is no local flow
      // step. However, we still want to represent that there's flow from the
      // operand to the instruction.
      nInstr = nOperand
    )
    or
    any(Stage0Output::Indirection ind).isAdditionalConversionFlow(operand, instr)
  }

  private predicate indirectionOperandFlow(RawIndirectOperandNode nodeFrom, Node nodeTo) {
    nodeFrom != nodeTo and
    (
      // Reduce the indirection count by 1 if we're passing through a `LoadInstruction`.
      exists(int ind, LoadInstruction load |
        hasOperandAndIndex(nodeFrom, load.getSourceAddressOperand(), ind) and
        nodeHasInstruction(nodeTo, load, ind - 1)
      )
      or
      // If an operand flows to an instruction, then the indirection of
      // the operand also flows to the indirection of the instruction.
      exists(Operand operand, Instruction instr, int indirectionIndex |
        simpleInstructionLocalFlowStep(operand, instr) and
        hasOperandAndIndex(nodeFrom, operand, pragma[only_bind_into](indirectionIndex)) and
        hasInstructionAndIndex(nodeTo, instr, pragma[only_bind_into](indirectionIndex))
      )
      or
      // If there's indirect flow to an operand, then there's also indirect
      // flow to the operand after applying some pointer arithmetic.
      exists(PointerArithmeticInstruction pointerArith, int indirectionIndex |
        hasOperandAndIndex(nodeFrom, pointerArith.getAnOperand(),
          pragma[only_bind_into](indirectionIndex)) and
        hasInstructionAndIndex(nodeTo, pointerArith, pragma[only_bind_into](indirectionIndex))
      )
    )
  }

  /**
   * Holds if `operand.getDef() = instr`, but there exists a `StoreInstruction` that
   * writes to an address that is equivalent to the value computed by `instr` in
   * between `instr` and `operand`, and therefore there should not be flow from `*instr`
   * to `*operand`.
   */
  pragma[nomagic]
  private predicate isStoredToBetween(Instruction instr, Operand operand) {
    simpleOperandLocalFlowStep(pragma[only_bind_into](instr), pragma[only_bind_into](operand)) and
    exists(StoreInstruction store, IRBlock block, int storeIndex, int instrIndex, int operandIndex |
      store.getDestinationAddress() = instr and
      block.getInstruction(storeIndex) = store and
      block.getInstruction(instrIndex) = instr and
      block.getInstruction(operandIndex) = operand.getUse() and
      instrIndex < storeIndex and
      storeIndex < operandIndex
    )
  }

  private predicate indirectionInstructionFlow(
    RawIndirectInstructionNode nodeFrom, IndirectOperandNode nodeTo
  ) {
    nodeFrom != nodeTo and
    // If there's flow from an instruction to an operand, then there's also flow from the
    // indirect instruction to the indirect operand.
    exists(Operand operand, Instruction instr, int indirectionIndex |
      simpleOperandLocalFlowStep(instr, operand)
    |
      hasOperandAndIndex(nodeTo, operand, pragma[only_bind_into](indirectionIndex)) and
      hasInstructionAndIndex(nodeFrom, instr, pragma[only_bind_into](indirectionIndex)) and
      not isStoredToBetween(instr, operand)
    )
  }

  predicate localFlowStep(Node nodeFrom, Node nodeTo) {
    exists(Stage0::Node nFrom, Stage0::Node nTo |
      nodeFrom = TNode0(nFrom) and
      nodeTo = TNode0(nTo) and
      Stage0::localFlowStep(nFrom, nTo)
    )
    or
    any(Stage0Output::Indirection ind)
        .isAdditionalConversionFlow(nodeFrom.asOperand(), nodeTo.asInstruction())
    or
    // Indirect operand -> (indirect) instruction flow
    indirectionOperandFlow(nodeFrom, nodeTo)
    or
    // Indirect instruction -> indirect operand flow
    indirectionInstructionFlow(nodeFrom, nodeTo)
  }

  class DataFlowCallable = Stage0::DataFlowCallable;

  DataFlowCallable nodeGetEnclosingCallable(Node n) {
    exists(Stage0::Node n0 |
      n = TNode0(n0) or n = TRawIndirectInstructionNode(n0, _) or n = TRawIndirectOperandNode(n0, _)
    |
      result = Stage0::nodeGetEnclosingCallable(n0)
    )
  }

  class DataFlowCall = CallInstruction;

  private newtype TPosition =
    TStage0Position(Stage0::Position pos) or
    TIndirectionPosition(int argumentIndex, int indirectionIndex) {
      Stage0Output::hasIndirectOperand(any(CallInstruction call).getArgumentOperand(argumentIndex),
        indirectionIndex)
    }

  class Position extends TPosition {
    string toString() {
      exists(int argumentIndex, int indirectionIndex |
        argumentIndex = this.getArgumentIndex() and indirectionIndex = this.getIndirectionIndex()
      |
        if argumentIndex = -1
        then
          if indirectionIndex = 0
          then result = "this pointer"
          else result = repeatStars(indirectionIndex - 1) + "this"
        else result = repeatStars(indirectionIndex) + argumentIndex
      )
    }

    int getIndirectionIndex() {
      this = TStage0Position(_) and
      result = 0
      or
      this = TIndirectionPosition(_, result)
    }

    int getArgumentIndex() {
      exists(Stage0::Position pos |
        this = TStage0Position(pos) and
        result = pos.getArgumentIndex()
      )
      or
      this = TIndirectionPosition(result, _)
    }
  }

  bindingset[argString]
  Position decodePosition(string argString) {
    exists(Stage0::Position pos |
      pos.getArgumentIndex() != -1 and
      pos = Stage0::decodePosition(argString) and
      result = TStage0Position(pos)
    )
    or
    exists(int indirection, string posString, int pos |
      argString = repeatStars(indirection) + posString and
      pos = AccessPath::parseInt(posString)
    |
      pos >= 0 and indirection > 0 and result = TIndirectionPosition(pos, indirection)
      or
      // `Argument[-1]` / `Parameter[-1]` is the qualifier object `*this`, not the `this` pointer itself.
      pos = -1 and result = TIndirectionPosition(pos, indirection + 1)
    )
  }

  abstract private class ArgumentNodeImpl extends Node {
    abstract predicate argumentOf(DataFlowCall call, Position pos);
  }

  final class ArgumentNode = ArgumentNodeImpl;

  final private class FinalNode0 = Node0;

  private class Stage0ArgumentNode extends ArgumentNodeImpl, FinalNode0 {
    Stage0::ArgumentNode argNode;

    Stage0ArgumentNode() { argNode = n }

    final override predicate argumentOf(DataFlowCall call, Position pos) {
      exists(Stage0::Position pos0 |
        pos = TStage0Position(pos0) and
        argNode.argumentOf(call, pos0)
      )
    }
  }

  private class IndirectArgumentNode extends ArgumentNodeImpl, IndirectOperandNode {
    DataFlowCall call;
    int argumentIndex;

    IndirectArgumentNode() {
      super.hasOperandAndIndirectionIndex(call.getArgumentOperand(argumentIndex), indirectionIndex)
    }

    override predicate argumentOf(DataFlowCall dfCall, Position pos) {
      pos = TIndirectionPosition(argumentIndex, pragma[only_bind_into](indirectionIndex)) and
      call = dfCall
    }
  }

  abstract private class ParameterNodeImpl extends Node {
    abstract predicate isParameterOf(DataFlowCallable f, Position pos);

    abstract Parameter getParameter(int indirectionIndex);
  }

  final class ParameterNode = ParameterNodeImpl;

  private class Stage0ParameterNode extends ParameterNodeImpl instanceof Node0 {
    Stage0::ParameterNode n;

    Stage0ParameterNode() { this = TNode0(n) }

    final override predicate isParameterOf(DataFlowCallable f, Position pos) {
      exists(Stage0::Position p |
        p.getArgumentIndex() = pos.getArgumentIndex() and
        pos.getIndirectionIndex() = 0 and
        n.isParameterOf(f, p)
      )
    }

    final override Parameter getParameter(int indirectionIndex) {
      result = n.getParameter(indirectionIndex)
    }
  }

  private class IndirectParameterNode extends ParameterNodeImpl {
    Stage0::ParameterNode node;
    int indirectionIndex;

    IndirectParameterNode() {
      this.(IndirectInstructionNode)
          .hasInstructionAndIndirectionIndex(node.asInstruction(), indirectionIndex)
      or
      this.(IndirectOperandNode).hasOperandAndIndirectionIndex(node.asOperand(), indirectionIndex)
    }

    final override Parameter getParameter(int indirectionIndex_) {
      result = node.getParameter() and indirectionIndex_ = indirectionIndex
    }

    final override predicate isParameterOf(DataFlowCallable f, Position pos) {
      exists(Stage0::Position p |
        p.getArgumentIndex() = pos.getArgumentIndex() and
        pos.getIndirectionIndex() = indirectionIndex and
        node.isParameterOf(f, p)
      )
    }
  }

  final private class BodyLessParameterNode extends NodeImpl, TBodyLessParameterNode {
    Stage0::ParameterNode paramNode;
    int indirectionIndex;

    BodyLessParameterNode() { this = TBodyLessParameterNode(paramNode, indirectionIndex) }

    final override Location getLocation() { result = paramNode.getLocation() }

    final override DataFlowType getType() {
      result = Stage0Output::getTypeImpl(paramNode.getType(), indirectionIndex)
    }

    final override Declaration getFunction() { result = paramNode.getFunction() }

    final override DataFlowCallable getEnclosingCallable() {
      result = paramNode.getEnclosingCallable()
    }

    final override string toString() { result = this.stars() + paramNode.toString() }

    final override string stars() { result = repeatStars(indirectionIndex) }

    final override predicate isGLValue() { none() }
  }

  private class BodylessParameterNodeParameter extends ParameterNodeImpl, BodyLessParameterNode {
    final override Parameter getParameter(int indirectionIndex_) {
      result = paramNode.getParameter() and
      indirectionIndex_ = indirectionIndex
    }

    final override predicate isParameterOf(DataFlowCallable f, Position pos) {
      exists(Stage0::Position p |
        p.getArgumentIndex() = pos.getArgumentIndex() and
        pos.getIndirectionIndex() = indirectionIndex and
        paramNode.isParameterOf(f, p)
      )
    }
  }

  /**
   * Holds if `node` is an indirect operand with columns `(operand, indirectionIndex)`, and
   * `operand` represents a use of the fully converted value of `call`.
   */
  private predicate callHasOperand(
    Node node, DataFlowCall call, int indirectionIndex, Stage0::OutNode n
  ) {
    exists(Operand operand |
      hasOperandAndIndex(node, operand, indirectionIndex) and
      n = Stage0::operandNode(operand) and
      n.getCall() = call
    )
  }

  /**
   * Holds if `node` is an indirect instruction with columns `(instr, indirectionIndex)`, and
   * `instr` represents a use of the fully converted value of `call`.
   *
   * Note that `hasOperand(node, _, _, _)` implies `not hasInstruction(node, _, _, _)`.
   */
  private predicate callHasInstruction(
    Node node, CallInstruction call, int indirectionIndex, Stage0::OutNode n
  ) {
    exists(Instruction instr |
      hasInstructionAndIndex(node, instr, indirectionIndex) and
      n = Stage0::instructionNode(instr) and
      n.getCall() = call
    )
  }

  private newtype TReturnKind =
    MkReturnKind(int indirectionIndex) {
      // derive a possible return indirection from SSA
      // (this is a more durable approach if SSA infers additional indirections for any reason)
      Stage0Output::hasIndirectOperand(any(ReturnValueAddress ret), indirectionIndex + 1)
      or
      // derive a possible return kind from the AST
      // (this approach includes functions declared that have no body; they may still have flow summaries)
      indirectionIndex =
        [0 .. max(Function f |
            not exists(f.getBlock())
          |
            Stage0Output::getMaxIndirectionsForType(f.getUnspecifiedType()) - 1
          )]
    }

  class ReturnKind extends MkReturnKind {
    int indirectionIndex;

    ReturnKind() { this = MkReturnKind(indirectionIndex) }

    final int getIndirectionIndex() { result = indirectionIndex }

    final string toString() { result = repeatStars(indirectionIndex) + "return" }
  }

  abstract private class OutNodeImpl extends Node {
    DataFlowCall call;

    DataFlowCall getCall() { result = call }

    abstract ReturnKind getReturnKind();
  }

  private class Stage0OutNode extends OutNodeImpl, FinalNode0 {
    Stage0::OutNode n;

    Stage0OutNode() { this = TNode0(n) and call = n.getCall() }

    final override ReturnKind getReturnKind() { result = MkReturnKind(0) }
  }

  final class OutNode = OutNodeImpl;

  /**
   * INTERNAL: do not use.
   *
   * A node representing the indirect value of a function call (i.e., a value hidden
   * behind a number of indirections).
   */
  private class IndirectReturnOutNode extends OutNodeImpl {
    int indirectionIndex;

    IndirectReturnOutNode() {
      // Annoyingly, we need to pick the fully converted value as the output of the function to
      // make flow through in the shared dataflow library work correctly.
      callHasOperand(this, call, indirectionIndex, _)
      or
      callHasInstruction(this, call, indirectionIndex, _)
    }

    CallInstruction getCallInstruction() { result = call }

    int getIndirectionIndex() { result = indirectionIndex }

    /** Gets the operand associated with this node, if any. */
    Operand getOperand() {
      exists(Stage0::OutNode n |
        callHasOperand(this, call, indirectionIndex, n) and
        result = n.asOperand()
      )
    }

    /** Gets the instruction associated with this node, if any. */
    Instruction getInstruction() {
      exists(Stage0::InstructionNode n |
        callHasInstruction(this, call, indirectionIndex, n) and
        result = n.asInstruction()
      )
    }

    final override ReturnKind getReturnKind() { result = MkReturnKind(indirectionIndex) }
  }

  abstract private class ReturnNodeImpl extends Node {
    abstract ReturnKind getKind();
  }

  private class ReturnValueAddress extends AddressOperand {
    ReturnValueAddress() { this = any(ReturnValueInstruction return).getReturnAddressOperand() }
  }

  private class RetNode extends ReturnNodeImpl, IndirectOperandNode {
    override ReturnValueAddress operand;

    final override ReturnKind getKind() {
      exists(Operand op |
        hasOperandAndIndex(this, pragma[only_bind_into](op), indirectionIndex) and
        result = MkReturnKind(indirectionIndex - 1)
      )
    }
  }

  final class ReturnNode = ReturnNodeImpl;

  class PostUpdateNode extends Node0 {
    override Stage0::PostUpdateNode n;

    Node getPreUpdateNode() { result = TNode0(n.getPreUpdateNode()) }

    int getIndirectionIndex() { result = n.getIndirectionIndex() }
  }

  predicate nodeIsHidden(Node node) {
    not node instanceof ArgumentNode and
    exists(Stage0::Node n | node = TNode0(n) | Stage0::nodeIsHidden(n))
  }
}
