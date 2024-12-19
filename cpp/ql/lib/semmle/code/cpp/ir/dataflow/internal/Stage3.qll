private import cpp as Cpp
private import semmle.code.cpp.ir.IR
private import semmle.code.cpp.models.interfaces.FunctionInputsAndOutputs as FIO
private import StageSig
private import Stage1
private import Stage2

module Stage3 implements StageSig {
  private newtype TNode =
    TNode2(Stage2::Node n) or
    TIteratorFlowNode(PhiNode phi)

  abstract private class NodeImpl extends TNode {
    abstract string toString();

    final Instruction asInstruction() { result = this.(InstructionNode).getInstruction() }

    final Operand asOperand() { result = this.(OperandNode).getOperand() }

    Cpp::Variable asVariable(int indirectionIndex) {
      exists(VariableNode var | var = this |
        result = var.getVariable() and
        indirectionIndex = var.getIndirectionIndex()
      )
    }

    abstract Cpp::Declaration getEnclosingCallable();

    abstract Cpp::Declaration getFunction();

    abstract DataFlowType getType();

    abstract Cpp::Location getLocation();

    predicate isGLValue() { none() }

    abstract predicate hasIndexInBlock(IRBlock block, int i);

    abstract string stars();
  }

  final class Node = NodeImpl;

  additional Node inject(Stage2::Node n) { result = TNode2(n) }

  private class Node2 extends TNode2, NodeImpl {
    Stage2::Node n;

    Node2() { this = TNode2(n) }

    override string toString() { result = n.toString() }

    final Instruction asInstruction() { result = this.(InstructionNode).getInstruction() }

    final Operand asOperand() { result = this.(OperandNode).getOperand() }

    final override Cpp::Declaration getEnclosingCallable() { result = n.getEnclosingCallable() }

    final override Cpp::Declaration getFunction() { result = n.getFunction() }

    final override DataFlowType getType() { result = n.getType() }

    final override Cpp::Location getLocation() { result = n.getLocation() }

    final override predicate isGLValue() { n.isGLValue() }

    final override string stars() { result = n.stars() }

    final override predicate hasIndexInBlock(IRBlock block, int i) { n.hasIndexInBlock(block, i) }
  }

  private class IteratorFlowNode extends TIteratorFlowNode, NodeImpl {
    PhiNode phi;

    IteratorFlowNode() { this = TIteratorFlowNode(phi) }

    override string toString() { result = phi.toString() }

    final override Cpp::Declaration getEnclosingCallable() {
      result = phi.getBasicBlock().getEnclosingFunction()
    }

    final override Cpp::Declaration getFunction() { result = this.getEnclosingCallable() }

    final override DataFlowType getType() { result = phi.getSourceVariable().getType() }

    final override Cpp::Location getLocation() { result = phi.getLocation() }

    final override predicate isGLValue() { none() }

    final override string stars() { result = repeatStars(phi.getSourceVariable().getIndirection()) }

    final override predicate hasIndexInBlock(IRBlock block, int i) { phi.definesAt(_, block, i, _) }
  }

  class OperandNode extends Node2 {
    override Stage2::OperandNode n;

    final Operand getOperand() { result = n.getOperand() }
  }

  class VariableNode extends Node2 {
    override Stage2::VariableNode n;

    final Cpp::Variable getVariable() { result = n.getVariable() }

    /** Gets the indirection index of this node. */
    int getIndirectionIndex() { result = n.getIndirectionIndex() }
  }

  OperandNode operandNode(Operand operand) { result.getOperand() = operand }

  class InstructionNode extends Node2 {
    override Stage2::InstructionNode n;

    Instruction getInstruction() { result = n.getInstruction() }
  }

  InstructionNode instructionNode(Instruction instr) { result.getInstruction() = instr }

  class IndirectOperandNode extends Node2 {
    override Stage2::IndirectOperandNode n;

    final predicate hasOperandAndIndirectionIndex(Operand operand, int indirectionIndex) {
      n.hasOperandAndIndirectionIndex(operand, indirectionIndex)
    }
  }

  class IndirectInstructionNode extends Node2 {
    override Stage2::IndirectInstructionNode n;

    final predicate hasInstructionAndIndirectionIndex(Instruction instr, int indirectionIndex) {
      n.hasInstructionAndIndirectionIndex(instr, indirectionIndex)
    }
  }

  class DataFlowCallable = Stage2::DataFlowCallable;

  class DataFlowCall = Stage2::DataFlowCall;

  DataFlowCallable nodeGetEnclosingCallable(Node node) { result = node.getEnclosingCallable() }

  class Position = Stage2::Position;

  class ReturnKind = Stage2::ReturnKind;

  predicate nodeIsHidden(Node node) {
    exists(Stage2::Node n | node = TNode2(n) and Stage2::nodeIsHidden(n))
  }

  class ArgumentNode extends Node2 {
    override Stage2::ArgumentNode n;

    predicate argumentOf(DataFlowCall call, Position pos) { n.argumentOf(call, pos) }
  }

  class ParameterNode extends Node2 {
    override Stage2::ParameterNode n;

    predicate isParameterOf(DataFlowCallable callable, Position pos) {
      n.isParameterOf(callable, pos)
    }

    Cpp::Parameter getParameter(int indirectionIndex) { result = n.getParameter(indirectionIndex) }
  }

  class OutNode extends Node2 {
    override Stage2::OutNode n;

    DataFlowCall getCall() { result = n.getCall() }

    ReturnKind getReturnKind() { result = n.getReturnKind() }
  }

  class ReturnNode extends Node2 {
    override Stage2::ReturnNode n;

    ReturnKind getKind() { result = n.getKind() }
  }

  predicate decodePosition = Stage2::decodePosition/1;

  class PostUpdateNode extends Node2 {
    override Stage2::PostUpdateNode n;

    Node getPreUpdateNode() { result = TNode2(n.getPreUpdateNode()) }

    int getIndirectionIndex() { result = n.getIndirectionIndex() }
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

  /* BEGIN ITERATOR LOGIC */
  private import codeql.ssa.Ssa as SsaImpl
  private import semmle.code.cpp.models.interfaces.Iterator as Interface
  private import semmle.code.cpp.models.implementations.Iterator as Impl

  private module SsaInput implements SsaImpl::InputSig<Cpp::Location> {
    import InputSigCommon

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
        exists(Stage2::OutNode out |
          out.getReturnKind().isReturnValue(0) and
          out.getCall() = starCall and
          out.asOperand() = address
        ) and
        bbStar.getInstruction(iStar) = starCall and
        Stage2::SsaCached::ssaDefReachesReadExt(_, def.asDef(), bbStar, iStar) and
        ultimate = getAnUltimateDefinition*(def) and
        beginStore = ultimate.getValue().asInstruction() and
        exists(Stage2::OutNode out |
          out.getReturnKind().isReturnValue(0) and
          out.getCall() = beginCall and
          out.asOperand() = beginStore.getSourceValueOperand()
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

  private import SsaInput

  private module IteratorSsa = SsaImpl::Make<Cpp::Location, SsaInput>;

  private class PhiNode extends IteratorSsa::DefinitionExt {
    PhiNode() {
      this instanceof IteratorSsa::PhiNode or
      this instanceof IteratorSsa::PhiReadNode
    }

    Node getNode() { result = TIteratorFlowNode(this) }
  }

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
    abstract Cpp::Location getLocation();
  }

  private class Def extends TDef, SsaDef {
    IteratorSsa::DefinitionExt def;

    Def() { this = TDef(def) }

    final override IteratorSsa::DefinitionExt asDef() { result = def }

    final override Cpp::Location getLocation() { result = this.getImpl().getLocation() }

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
    Node getValue() { result = TNode2(Stage2::inject(Stage1::inject(this.getImpl().getValue()))) }

    /** Gets the indirection index of this definition. */
    int getIndirectionIndex() { result = this.getImpl().getIndirectionIndex() }
  }

  private class Phi extends TPhi, SsaDef {
    PhiNode phi;

    Phi() { this = TPhi(phi) }

    final override PhiNode asPhi() { result = phi }

    final override Cpp::Location getLocation() { result = phi.getBasicBlock().getLocation() }

    override string toString() { result = phi.toString() }

    Node getNode() { result = TIteratorFlowNode(phi) }
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

  /* END ITERATOR LOGIC */
  predicate localFlowStep(Node nodeFrom, Node nodeTo) {
    exists(Stage2::Node nFrom, Stage2::Node nTo |
      nodeFrom = TNode2(nFrom) and
      nodeTo = TNode2(nTo) and
      Stage2::localFlowStep(nFrom, nTo)
    )
    or
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

  additional predicate jumpStep(Node node1, Node node2) {
    exists(Stage2::Node n1, Stage2::Node n2 |
      node1 = TNode2(n1) and
      node2 = TNode2(n2) and
      Stage2::jumpStep(n1, n2)
    )
  }

  additional class Content = Stage2::Content;

  additional class FieldContent = Stage2::FieldContent;

  additional class UnionContent = Stage2::UnionContent;

  additional class ElementContent = Stage2::ElementContent;

  additional predicate storeStep(Node node1, Content c, Node node2, boolean certain) {
    exists(Stage2::Node n1, Stage2::Node n2 |
      node1 = TNode2(n1) and
      node2 = TNode2(n2) and
      Stage2::storeStep(n1, c, n2, certain)
    )
  }

  additional predicate readStep(Node node1, Content c, Node node2) {
    exists(Stage2::Node n1, Stage2::Node n2 |
      node1 = TNode2(n1) and
      node2 = TNode2(n2) and
      Stage2::readStep(n1, c, n2)
    )
  }

  additional class SsaPhiInputNode extends Node2 {
    override Stage2::SsaPhiInputNode n;
  }

  additional class SsaPhiNode extends Node2 {
    override Stage2::SsaPhiNode n;

    Stage2::SourceVariable getSourceVariable() { result = n.getSourceVariable() }

    Node getAnInput() { result = inject(n.getAnInput()) }

    Node getAnInput(boolean fromBackEdge) { result = inject(n.getAnInput(fromBackEdge)) }

    predicate isPhiRead() { n.isPhiRead() }
  }

  additional class ArgumentOutNode extends Node2 {
    override Stage2::ArgumentOutNode n;

    int getArgumentIndex() { result = n.getArgumentIndex() }

    ArgumentOperand getOperand() { result = n.getOperand() }

    int getIndirectionIndex() { result = n.getIndirectionIndex() }

    CallInstruction getCallInstruction() { result = n.getCallInstruction() }

    /**
     * Gets the `Function` that the call targets, if this is statically known.
     */
    Cpp::Function getStaticCallTarget() { result = this.getCallInstruction().getStaticCallTarget() }
  }

  additional class UninitializedNode extends Node2 {
    override Stage2::UninitializedNode n;

    /** Gets the uninitialized local variable corresponding to this node. */
    Cpp::LocalVariable getLocalVariable() { result = n.getLocalVariable() }
  }

  additional Node callInput(CallInstruction call, FIO::FunctionInput input) {
    result = TNode2(Stage2::callInput(call, input))
  }

  additional Node callOutput(CallInstruction call, FIO::FunctionOutput output, int indirectionIndex) {
    result = TNode2(Stage2::callOutput(call, output, indirectionIndex))
  }
}
