private import cpp
private import Base
private import semmle.code.cpp.ir.IR
private import StageSig
private import Stage0
private import codeql.dataflow.internal.AccessPathSyntax as AccessPath

module Stage1 implements StageSig {
  additional newtype TNode =
    additional TNode0(Stage0::Node n) or
    additional TRawIndirectOperand(Stage0::Node node, int indirectionIndex) {
      Stage0Output::hasRawIndirectOperand(node.asOperand(), indirectionIndex)
    } or
    additional TRawIndirectInstruction(Stage0::Node node, int indirectionIndex) {
      not exists(node.asOperand()) and
      Stage0Output::hasRawIndirectInstruction(node.asInstruction(), indirectionIndex)
    }

  abstract class Node extends TNode {
    abstract string toString();

    abstract Instruction asInstruction();

    abstract Operand asOperand();

    abstract Declaration getEnclosingCallable();

    abstract Declaration getFunction();

    abstract DataFlowType getType();

    abstract Location getLocation();

    abstract predicate isGLValue();

    abstract string stars();

    predicate hasIndexInBlock(IRBlock block, int i) {
      exists(Stage0::Node n0 |
        this = TNode0(n0)
        or
        this = TRawIndirectOperand(n0, _)
        or
        this = TRawIndirectInstruction(n0, _)
      |
        n0.hasIndexInBlock(block, i)
      )
    }
  }

  private class Node0 extends Node, TNode0 {
    Stage0::Node n;

    Node0() { this = TNode0(n) }

    override string toString() { result = n.toString() }

    final override Instruction asInstruction() { result = n.asInstruction() }

    final override Operand asOperand() { result = n.asOperand() }

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
   * INTERNAL: Do not use.
   *
   * A node that represents the indirect value of an operand in the IR
   * after `index` number of loads.
   */
  private class RawIndirectOperand0 extends Node, TRawIndirectOperand {
    Stage0::Node node;
    int indirectionIndex;

    RawIndirectOperand0() { this = TRawIndirectOperand(node, indirectionIndex) }

    final override Operand asOperand() { none() }

    final override Instruction asInstruction() { none() }

    /** Gets the underlying instruction. */
    Operand getOperand() { result = node.asOperand() }

    /** Gets the underlying indirection index. */
    int getIndirectionIndex() { result = indirectionIndex }

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

    override string toString() { result = this.stars() + operandNode(this.getOperand()).toString() }

    final override string stars() {
      result = strictconcat(int i | i = [1 .. indirectionIndex] | "*")
    }
  }

  /**
   * INTERNAL: Do not use.
   *
   * A node that represents the indirect value of an instruction in the IR
   * after `index` number of loads.
   */
  private class RawIndirectInstruction0 extends Node, TRawIndirectInstruction {
    Stage0::Node node;
    int indirectionIndex;

    RawIndirectInstruction0() { this = TRawIndirectInstruction(node, indirectionIndex) }

    final override Operand asOperand() { none() }

    final override Instruction asInstruction() { none() }

    /** Gets the underlying instruction. */
    Instruction getInstruction() { result = node.asInstruction() }

    /** Gets the underlying indirection index. */
    int getIndirectionIndex() { result = indirectionIndex }

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

    override string toString() {
      result = this.stars() + instructionNode(this.getInstruction()).toString()
    }

    final override string stars() {
      result = strictconcat(int i | i = [1 .. indirectionIndex] | "*")
    }
  }

  /**
   * INTERNAL: Do not use.
   *
   * A node that represents the indirect value of an operand in the IR
   * after a number of loads.
   */
  private class RawIndirectOperand extends Node {
    int indirectionIndex;
    Operand operand;

    RawIndirectOperand() {
      exists(Stage0::Node node | operand = node.asOperand() |
        this = TRawIndirectOperand(node, indirectionIndex)
        or
        this = TRawIndirectInstruction(node, indirectionIndex)
      )
    }

    /** Gets the operand associated with this node. */
    Operand getOperand() { result = operand }

    /** Gets the underlying indirection index. */
    int getIndirectionIndex() { result = indirectionIndex }

    final override string toString() {
      result = [this.(RawIndirectOperand0).toString(), this.(RawIndirectInstruction0).toString()]
    }

    final override Instruction asInstruction() {
      result =
        [this.(RawIndirectOperand0).asInstruction(), this.(RawIndirectInstruction0).asInstruction()]
    }

    final override Operand asOperand() {
      result = [this.(RawIndirectOperand0).asOperand(), this.(RawIndirectInstruction0).asOperand()]
    }

    final override Declaration getEnclosingCallable() {
      result =
        [
          this.(RawIndirectOperand0).getEnclosingCallable(),
          this.(RawIndirectInstruction0).getEnclosingCallable()
        ]
    }

    final override Declaration getFunction() {
      result =
        [this.(RawIndirectOperand0).getFunction(), this.(RawIndirectInstruction0).getFunction()]
    }

    final override DataFlowType getType() {
      result = [this.(RawIndirectOperand0).getType(), this.(RawIndirectInstruction0).getType()]
    }

    final override Location getLocation() {
      result =
        [this.(RawIndirectOperand0).getLocation(), this.(RawIndirectInstruction0).getLocation()]
    }

    final override predicate isGLValue() {
      this.(RawIndirectOperand0).isGLValue() or this.(RawIndirectInstruction0).isGLValue()
    }

    final override string stars() {
      result = [this.(RawIndirectOperand0).stars(), this.(RawIndirectInstruction0).stars()]
    }
  }

  /**
   * INTERNAL: Do not use.
   *
   * A node that represents the indirect value of an instruction in the IR
   * after a number of loads.
   */
  private class RawIndirectInstruction extends Node {
    int indirectionIndex;
    Instruction instr;

    RawIndirectInstruction() {
      exists(Stage0::Node node | instr = node.asInstruction() |
        this = TRawIndirectOperand(node, indirectionIndex)
        or
        this = TRawIndirectInstruction(node, indirectionIndex)
      )
    }

    /** Gets the instruction associated with this node. */
    Instruction getInstruction() { result = instr }

    /** Gets the underlying indirection index. */
    int getIndirectionIndex() { result = indirectionIndex }

    final override string toString() {
      result = [this.(RawIndirectOperand0).toString(), this.(RawIndirectInstruction0).toString()]
    }

    final override Instruction asInstruction() {
      result =
        [this.(RawIndirectOperand0).asInstruction(), this.(RawIndirectInstruction0).asInstruction()]
    }

    final override Operand asOperand() {
      result = [this.(RawIndirectOperand0).asOperand(), this.(RawIndirectInstruction0).asOperand()]
    }

    final override Declaration getEnclosingCallable() {
      result =
        [
          this.(RawIndirectOperand0).getEnclosingCallable(),
          this.(RawIndirectInstruction0).getEnclosingCallable()
        ]
    }

    final override Declaration getFunction() {
      result =
        [this.(RawIndirectOperand0).getFunction(), this.(RawIndirectInstruction0).getFunction()]
    }

    final override DataFlowType getType() {
      result = [this.(RawIndirectOperand0).getType(), this.(RawIndirectInstruction0).getType()]
    }

    final override Location getLocation() {
      result =
        [this.(RawIndirectOperand0).getLocation(), this.(RawIndirectInstruction0).getLocation()]
    }

    final override predicate isGLValue() {
      this.(RawIndirectOperand0).isGLValue() or this.(RawIndirectInstruction0).isGLValue()
    }

    final override string stars() {
      result = [this.(RawIndirectOperand0).stars(), this.(RawIndirectInstruction0).stars()]
    }
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
  abstract class IndirectOperandNode extends Node {
    /** Gets the underlying operand and the underlying indirection index. */
    abstract predicate hasOperandAndIndirectionIndex(Operand operand, int indirectionIndex);
  }

  private class IndirectOperandFromRaw extends IndirectOperandNode, RawIndirectOperand {
    override predicate hasOperandAndIndirectionIndex(Operand operand_, int indirectionIndex_) {
      operand_ = RawIndirectOperand.super.getOperand() and
      indirectionIndex_ = RawIndirectOperand.super.getIndirectionIndex()
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

  private class IndirectOperandFromIRRepr extends IndirectOperandNode {
    Operand operand;
    int indirectionIndex;

    IndirectOperandFromIRRepr() {
      exists(Operand repr, int indirectionIndexRepr |
        Stage0Output::hasIRRepresentationOfIndirectOperand(operand, indirectionIndex, repr,
          indirectionIndexRepr) and
        nodeHasOperand(this, repr, indirectionIndexRepr)
      )
    }

    override predicate hasOperandAndIndirectionIndex(Operand op, int index) {
      op = operand and index = indirectionIndex
    }

    final override string toString() {
      result = [this.(InstructionNode).toString(), this.(RawIndirectOperand).toString()]
    }

    final override Instruction asInstruction() {
      result = [this.(InstructionNode).asInstruction(), this.(RawIndirectOperand).asInstruction()]
    }

    final override Operand asOperand() {
      result = [this.(InstructionNode).asOperand(), this.(RawIndirectOperand).asOperand()]
    }

    final override Declaration getEnclosingCallable() {
      result =
        [
          this.(InstructionNode).getEnclosingCallable(),
          this.(RawIndirectOperand).getEnclosingCallable()
        ]
    }

    final override Declaration getFunction() {
      result =
        [
          this.(InstructionNode).getFunction(),
          this.(RawIndirectOperand).getFunction()
        ]
    }

    final override DataFlowType getType() {
      result =
        [
          this.(InstructionNode).getType(),
          this.(RawIndirectOperand).getType()
        ]
    }

    final override Location getLocation() {
      result =
        [
          this.(InstructionNode).getLocation(),
          this.(RawIndirectOperand).getLocation()
        ]
    }

    final override predicate isGLValue() {
      this.(InstructionNode).isGLValue()
      or
      this.(RawIndirectOperand).isGLValue()
    }

    final override string stars() {
      result =
        [
          this.(InstructionNode).stars(),
          this.(RawIndirectOperand).stars()
        ]
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
  abstract class IndirectInstructionNode extends Node {
    /** Gets the underlying operand and the underlying indirection index. */
    abstract predicate hasInstructionAndIndirectionIndex(Instruction instr, int index);
  }

  private class IndirectInstructionFromRaw extends IndirectInstructionNode, RawIndirectInstruction {
    override predicate hasInstructionAndIndirectionIndex(Instruction instr_, int index_) {
      instr_ = RawIndirectInstruction.super.getInstruction() and
      index_ = RawIndirectInstruction.super.getIndirectionIndex()
    }
  }

  private class IndirectInstructionFromIRRepr extends IndirectInstructionNode {
    Instruction instr;
    int indirectionIndex;

    IndirectInstructionFromIRRepr() {
      exists(Instruction repr, int indirectionIndexRepr |
        Stage0Output::hasIRRepresentationOfIndirectInstruction(instr, indirectionIndex, repr,
          indirectionIndexRepr) and
        nodeHasInstruction(this, repr, indirectionIndexRepr)
      )
    }

    override predicate hasInstructionAndIndirectionIndex(Instruction i, int index) {
      i = instr and index = indirectionIndex
    }

    final override string toString() {
      result = [this.(InstructionNode).toString(), this.(RawIndirectInstruction).toString()]
    }

    final override Instruction asInstruction() {
      result =
        [this.(InstructionNode).asInstruction(), this.(RawIndirectInstruction).asInstruction()]
    }

    final override Operand asOperand() {
      result = [this.(InstructionNode).asOperand(), this.(RawIndirectInstruction).asOperand()]
    }

    final override Declaration getEnclosingCallable() {
      result =
        [
          this.(InstructionNode).getEnclosingCallable(),
          this.(RawIndirectInstruction).getEnclosingCallable()
        ]
    }

    final override Declaration getFunction() {
      result =
        [
          this.(InstructionNode).getFunction(),
          this.(RawIndirectInstruction).getFunction()
        ]
    }

    final override DataFlowType getType() {
      result =
        [
          this.(InstructionNode).getType(),
          this.(RawIndirectInstruction).getType()
        ]
    }

    final override Location getLocation() {
      result =
        [
          this.(InstructionNode).getLocation(),
          this.(RawIndirectInstruction).getLocation()
        ]
    }

    final override predicate isGLValue() {
      this.(InstructionNode).isGLValue()
      or
      this.(RawIndirectInstruction).isGLValue()
    }

    final override string stars() {
      result =
        [
          this.(InstructionNode).stars(),
          this.(RawIndirectInstruction).stars()
        ]
    }
  }

  private predicate simpleOperandLocalFlowStep(Instruction instr, Operand operand) {
    exists(Stage0::Node nInstr, Stage0::Node nOperand |
      nInstr.asInstruction() = instr and
      nOperand.asOperand() = operand and
      Stage0::localFlowStep(nInstr, nOperand)
    )
  }

  private predicate simpleInstructionLocalFlowStep(Operand operand, Instruction instr) {
    exists(Stage0::Node nInstr, Stage0::Node nOperand |
      nInstr.asInstruction() = instr and
      nOperand.asOperand() = operand and
      Stage0::localFlowStep(nOperand, nInstr)
    )
  }

  private predicate indirectionOperandFlow(RawIndirectOperand nodeFrom, Node nodeTo) {
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
    RawIndirectInstruction nodeFrom, IndirectOperandNode nodeTo
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
    // Indirect operand -> (indirect) instruction flow
    indirectionOperandFlow(nodeFrom, nodeTo)
    or
    // Indirect instruction -> indirect operand flow
    indirectionInstructionFlow(nodeFrom, nodeTo)
  }

  class DataFlowCallable = Stage0::DataFlowCallable;

  DataFlowCallable nodeGetEnclosingCallable(Node n) {
    exists(Stage0::Node n0 |
      n = TNode0(n0) or n = TRawIndirectInstruction(n0, _) or n = TRawIndirectOperand(n0, _)
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

  abstract class ArgumentNode instanceof Node {
    abstract string toString();

    abstract predicate argumentOf(DataFlowCall call, Position pos);
  }

  private class Stage0ArgumentNode extends ArgumentNode, Node0 {
    override Stage0::ArgumentNode n;

    final override string toString() { result = n.toString() }

    final override predicate argumentOf(DataFlowCall call, Position pos) {
      exists(Stage0::Position pos0 |
        pos = TStage0Position(pos0) and
        n.argumentOf(call, pos0)
      )
    }
  }

  private class IndirectArgumentNode extends ArgumentNode instanceof IndirectOperandNode {
    DataFlowCall call;
    int argumentIndex;
    int indirectionIndex;

    IndirectArgumentNode() {
      super.hasOperandAndIndirectionIndex(call.getArgumentOperand(argumentIndex), indirectionIndex)
    }

    final override string toString() { result = IndirectOperandNode.super.toString() }

    override predicate argumentOf(DataFlowCall dfCall, Position pos) {
      pos = TIndirectionPosition(argumentIndex, pragma[only_bind_into](indirectionIndex)) and
      call = dfCall
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
    TStage0ReturnKind(Stage0::ReturnKind kind) or
    TRetKind(int indirectionIndex) {
      // derive a possible return indirection from SSA
      // (this is a more durable approach if SSA infers additional indirections for any reason)
      Stage0Output::hasIndirectOperand(any(ReturnValueInstruction ret).getReturnAddressOperand(),
        indirectionIndex + 1) // We subtract one because the return loads the value.
      or
      // derive a possible return kind from the AST
      // (this approach includes functions declared that have no body; they may still have flow summaries)
      indirectionIndex =
        [0 .. max(Function f |
            not exists(f.getBlock())
          |
            Stage0Output::getMaxIndirectionsForType(f.getUnspecifiedType()) - 1 // -1 because a returned value is a prvalue not a glvalue
          )]
    }

  abstract class ReturnKind extends TReturnKind {
    abstract int getIndirectionIndex();

    abstract string toString();
  }

  private class Stage0ReturnKind extends ReturnKind, TStage0ReturnKind {
    Stage0::ReturnKind kind;

    Stage0ReturnKind() { this = TStage0ReturnKind(kind) }

    final override int getIndirectionIndex() { result = kind.getIndirectionIndex() }

    final override string toString() { result = kind.toString() }
  }

  private class RetKind extends ReturnKind, TRetKind {
    int indirectionIndex;

    RetKind() { this = TRetKind(indirectionIndex) }

    final override int getIndirectionIndex() { result = indirectionIndex }

    final override string toString() { result = repeatStars(indirectionIndex) + "return" }
  }

  abstract private class OutNodeImpl instanceof Node {
    DataFlowCall call;

    DataFlowCall getCall() { result = call }

    abstract ReturnKind getReturnKind();

    abstract string toString();
  }

  private class Stage0OutNode extends OutNodeImpl, Node0 {
    override Stage0::OutNode n;

    Stage0OutNode() { call = n.getCall() }

    final override ReturnKind getReturnKind() { result = TStage0ReturnKind(n.getReturnKind()) }

    final override string toString() { result = Node0.super.toString() }
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

    final override ReturnKind getReturnKind() { result = TRetKind(indirectionIndex) }

    final override string toString() {
      result = [this.(IndirectOperandNode).toString(), this.(IndirectInstructionNode).toString()]
    }
  }

  abstract private class ReturnNodeImpl instanceof Node {
    abstract ReturnKind getKind();

    abstract string toString();
  }

  private class Stage0ReturnNode extends ReturnNodeImpl, Node0 {
    override Stage0::ReturnNode n;

    final override ReturnKind getKind() { result = TStage0ReturnKind(n.getKind()) }

    final override string toString() { result = Node0.super.toString() }
  }

  private class RetNode extends ReturnNodeImpl instanceof IndirectOperandNode {
    final override ReturnKind getKind() {
      exists(Operand op, int indirectionIndex |
        hasOperandAndIndex(this, pragma[only_bind_into](op), indirectionIndex + 1)
      |
        op = any(ReturnValueInstruction return).getReturnAddressOperand() and
        result = TRetKind(indirectionIndex)
      )
    }

    final override string toString() { result = IndirectOperandNode.super.toString() }
  }

  final class ReturnNode = ReturnNodeImpl;

  class PostUpdateNode extends Node0 {
    override Stage0::PostUpdateNode n;

    Node getPreUpdateNode() { result = TNode0(n.getPreUpdateNode()) }
  }
}
