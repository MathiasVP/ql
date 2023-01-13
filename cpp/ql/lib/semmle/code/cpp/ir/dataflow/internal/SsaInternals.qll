private import codeql.ssa.Ssa as SsaImplCommon
private import semmle.code.cpp.ir.IR
private import DataFlowUtil
private import DataFlowImplCommon as DataFlowImplCommon
private import semmle.code.cpp.models.interfaces.Allocation as Alloc
private import semmle.code.cpp.models.interfaces.DataFlow as DataFlow
private import semmle.code.cpp.ir.internal.IRCppLanguage
private import DataFlowPrivate
private import ssa0.SsaInternals as SsaInternals0
import SsaInternalsCommon

private module SourceVariables {
  int getMaxIndirectionForIRVariable(IRVariable var) {
    exists(Type type, boolean isGLValue |
      var.getLanguageType().hasType(type, isGLValue) and
      if isGLValue = true
      then result = 1 + getMaxIndirectionsForType(type)
      else result = getMaxIndirectionsForType(type)
    )
  }

  cached
  private newtype TSourceVariable =
    TSourceIRVariable(BaseIRVariable baseVar, int ind) {
      ind = [0 .. getMaxIndirectionForIRVariable(baseVar.getIRVariable())]
    } or
    TCallVariable(AllocationInstruction call, int ind) {
      ind = [0 .. countIndirectionsForCppType(getResultLanguageType(call))]
    }

  abstract class SourceVariable extends TSourceVariable {
    int ind;

    bindingset[ind]
    SourceVariable() { any() }

    abstract string toString();

    int getIndirection() { result = ind }

    abstract BaseSourceVariable getBaseVariable();
  }

  class SourceIRVariable extends SourceVariable, TSourceIRVariable {
    BaseIRVariable var;

    SourceIRVariable() { this = TSourceIRVariable(var, ind) }

    IRVariable getIRVariable() { result = var.getIRVariable() }

    override BaseIRVariable getBaseVariable() { result.getIRVariable() = this.getIRVariable() }

    override string toString() {
      ind = 0 and
      result = this.getIRVariable().toString()
      or
      ind > 0 and
      result = this.getIRVariable().toString() + " indirection"
    }
  }

  class CallVariable extends SourceVariable, TCallVariable {
    AllocationInstruction call;

    CallVariable() { this = TCallVariable(call, ind) }

    AllocationInstruction getCall() { result = call }

    override BaseCallVariable getBaseVariable() { result.getCallInstruction() = call }

    override string toString() {
      ind = 0 and
      result = "Call"
      or
      ind > 0 and
      result = "Call indirection"
    }
  }
}

import SourceVariables

/**
 * Holds if the `(operand, indirectionIndex)` columns should be
 * assigned a `RawIndirectOperand` value.
 */
predicate hasRawIndirectOperand(Operand op, int indirectionIndex) {
  exists(CppType type, int m |
    not ignoreOperand(op) and
    type = getLanguageType(op) and
    m = countIndirectionsForCppType(type) and
    indirectionIndex = [1 .. m] and
    not exists(getIRRepresentationOfIndirectOperand(op, indirectionIndex))
  )
}

/**
 * Holds if the `(instr, indirectionIndex)` columns should be
 * assigned a `RawIndirectInstruction` value.
 */
predicate hasRawIndirectInstruction(Instruction instr, int indirectionIndex) {
  exists(CppType type, int m |
    not ignoreInstruction(instr) and
    type = getResultLanguageType(instr) and
    m = countIndirectionsForCppType(type) and
    indirectionIndex = [1 .. m] and
    not exists(getIRRepresentationOfIndirectInstruction(instr, indirectionIndex))
  )
}

cached
private newtype TDefOrUseImpl =
  TDefImpl(Operand address, int indirectionIndex) {
    exists(Instruction base | isDef(_, _, address, base, _, indirectionIndex) |
      // We only include the definition if the SSA pruning stage
      // concluded that the definition is live after the write.
      any(SsaInternals0::Def def).getAddressOperand() = address
      or
      // Since the pruning stage doesn't know about global variables we can't use the above check to
      // rule out dead assignments to globals.
      base.(VariableAddressInstruction).getAstVariable() instanceof Cpp::GlobalOrNamespaceVariable
    )
  } or
  TUseImpl(Operand operand, int indirectionIndex) {
    isUse(_, operand, _, _, indirectionIndex) and
    not isDef(_, _, operand, _, _, _)
  } or
  TGlobalUse(Cpp::GlobalOrNamespaceVariable v, IRFunction f, int indirectionIndex) {
    // Represents a final "use" of a global variable to ensure that
    // the assignment to a global variable isn't ruled out as dead.
    exists(VariableAddressInstruction vai, int defIndex |
      vai.getEnclosingIRFunction() = f and
      vai.getAstVariable() = v and
      isDef(_, _, _, vai, _, defIndex) and
      indirectionIndex = [0 .. defIndex] + 1
    )
  } or
  TGlobalDef(Cpp::GlobalOrNamespaceVariable v, IRFunction f, int indirectionIndex) {
    // Represents the initial "definition" of a global variable when entering
    // a function body.
    exists(VariableAddressInstruction vai |
      vai.getEnclosingIRFunction() = f and
      vai.getAstVariable() = v and
      isUse(_, _, vai, _, indirectionIndex) and
      not isDef(_, _, vai.getAUse(), _, _, _)
    )
  } or
  TIteratorDef(
    Operand iteratorAddress, BaseSourceVariableInstruction container, int indirectionIndex
  ) {
    isIteratorDef(container, iteratorAddress, _, _, indirectionIndex) and
    any(SsaInternals0::Def def | def.isIteratorDef()).getAddressOperand() = iteratorAddress
  } or
  TIteratorUse(
    Operand iteratorAddress, BaseSourceVariableInstruction container, int indirectionIndex
  ) {
    isIteratorUse(container, iteratorAddress, _, indirectionIndex)
  }

abstract private class DefOrUseImpl extends TDefOrUseImpl {
  /** Gets a textual representation of this element. */
  abstract string toString();

  /** Gets the block of this definition or use. */
  abstract IRBlock getBlock();

  /** Holds if this definition or use has index `index` in block `block`. */
  abstract predicate hasIndexInBlock(IRBlock block, int index);

  final predicate hasIndexInBlock(IRBlock block, int index, SourceVariable sv) {
    this.hasIndexInBlock(block, index) and
    sv = this.getSourceVariable()
  }

  /** Gets the location of this element. */
  abstract Cpp::Location getLocation();

  /**
   * Gets the index (i.e., the number of loads required) of this
   * definition or use.
   *
   * Note that this is _not_ the definition's (or use's) index in
   * the enclosing basic block. To obtain this index, use
   * `DefOrUseImpl::hasIndexInBlock/2` or `DefOrUseImpl::hasIndexInBlock/3`.
   */
  abstract int getIndirectionIndex();

  /**
   * Gets the instruction that computes the base of this definition or use.
   * This is always a `VariableAddressInstruction` or an `AllocationInstruction`.
   */
  abstract BaseSourceVariableInstruction getBase();

  final BaseSourceVariable getBaseSourceVariable() {
    this.getBase().getBaseSourceVariable() = result
  }

  /** Gets the variable that is defined or used. */
  final SourceVariable getSourceVariable() {
    exists(BaseSourceVariable v, int ind |
      sourceVariableHasBaseAndIndex(result, v, ind) and
      defOrUseHasSourceVariable(this, v, ind)
    )
  }
}

private predicate defOrUseHasSourceVariable(DefOrUseImpl defOrUse, BaseSourceVariable bv, int ind) {
  defHasSourceVariable(defOrUse, bv, ind)
  or
  useHasSourceVariable(defOrUse, bv, ind)
}

pragma[noinline]
private predicate defHasSourceVariable(DefImpl def, BaseSourceVariable bv, int ind) {
  bv = def.getBaseSourceVariable() and
  ind = def.getIndirection()
}

pragma[noinline]
private predicate useHasSourceVariable(UseImpl use, BaseSourceVariable bv, int ind) {
  bv = use.getBaseSourceVariable() and
  ind = use.getIndirection()
}

pragma[noinline]
private predicate sourceVariableHasBaseAndIndex(SourceVariable v, BaseSourceVariable bv, int ind) {
  v.getBaseVariable() = bv and
  v.getIndirection() = ind
}

abstract class DefImpl extends DefOrUseImpl {
  Operand address;
  int ind;

  bindingset[ind]
  DefImpl() { any() }

  abstract int getIndirection();

  abstract Node0Impl getValue();

  abstract predicate isCertain();

  Operand getAddressOperand() { result = address }

  override int getIndirectionIndex() { result = ind }

  override string toString() { result = "DefImpl" }

  override IRBlock getBlock() { result = this.getAddressOperand().getUse().getBlock() }

  override Cpp::Location getLocation() { result = this.getAddressOperand().getUse().getLocation() }

  final override predicate hasIndexInBlock(IRBlock block, int index) {
    this.getAddressOperand().getUse() = block.getInstruction(index)
  }
}

private class DirectDef extends DefImpl, TDefImpl {
  DirectDef() { this = TDefImpl(address, ind) }

  override BaseSourceVariableInstruction getBase() { isDef(_, _, address, result, _, _) }

  override int getIndirection() { isDef(_, _, address, _, result, ind) }

  override Node0Impl getValue() { isDef(_, result, address, _, _, _) }

  override predicate isCertain() { isDef(true, _, address, _, _, ind) }
}

private class IteratorDef extends DefImpl, TIteratorDef {
  BaseSourceVariableInstruction container;

  IteratorDef() { this = TIteratorDef(address, container, ind) }

  override BaseSourceVariableInstruction getBase() { result = container }

  override int getIndirection() { isIteratorDef(container, address, _, result, ind) }

  override Node0Impl getValue() { isIteratorDef(container, address, result, _, _) }

  override predicate isCertain() { none() }
}

abstract class UseImpl extends DefOrUseImpl {
  Operand operand;
  int ind;

  bindingset[ind]
  UseImpl() { any() }

  Operand getOperand() { result = operand }

  override string toString() { result = "UseImpl" }

  final override predicate hasIndexInBlock(IRBlock block, int index) {
    operand.getUse() = block.getInstruction(index)
  }

  final override IRBlock getBlock() { result = operand.getUse().getBlock() }

  final override Cpp::Location getLocation() { result = operand.getLocation() }

  override int getIndirectionIndex() { result = ind }

  abstract int getIndirection();

  abstract predicate isCertain();
}

private class DirectUse extends UseImpl, TUseImpl {
  DirectUse() { this = TUseImpl(operand, ind) }

  override int getIndirection() { isUse(_, operand, _, result, ind) }

  override BaseSourceVariableInstruction getBase() { isUse(_, operand, result, _, ind) }

  override predicate isCertain() { isUse(true, operand, _, _, ind) }
}

private class IteratorUse extends UseImpl, TIteratorUse {
  BaseSourceVariableInstruction container;

  IteratorUse() { this = TIteratorUse(operand, container, ind) }

  override int getIndirection() { isIteratorUse(container, operand, result, ind) }

  override BaseSourceVariableInstruction getBase() { result = container }

  override predicate isCertain() { none() }
}

class GlobalUse extends TGlobalUse {
  Cpp::GlobalOrNamespaceVariable global;
  IRFunction f;
  int indirectionIndex;

  GlobalUse() { this = TGlobalUse(global, f, indirectionIndex) }

  Cpp::GlobalOrNamespaceVariable getVariable() { result = global }

  IRFunction getIRFunction() { result = f }

  final predicate hasIndexInBlock(IRBlock block, int index) {
    exists(ExitFunctionInstruction exit |
      exit = f.getExitFunctionInstruction() and
      block.getInstruction(index) = exit
    )
  }

  int getIndirectionIndex() { result = indirectionIndex }

  SourceVariable getSourceVariable() { sourceVariableIsGlobal(result, global, f, indirectionIndex) }

  final predicate hasIndexInBlock(IRBlock block, int index, SourceVariable sv) {
    this.hasIndexInBlock(block, index) and
    sv = this.getSourceVariable()
  }

  final Cpp::Location getLocation() { result = f.getLocation() }

  string toString() {
    if indirectionIndex = 1
    then result = global.toString()
    else result = global.toString() + " indirection"
  }

  Type getUnspecifiedType() { result = global.getUnspecifiedType() }
}

class GlobalDef extends TGlobalDef {
  Cpp::GlobalOrNamespaceVariable global;
  IRFunction f;
  int indirectionIndex;

  GlobalDef() { this = TGlobalDef(global, f, indirectionIndex) }

  Cpp::GlobalOrNamespaceVariable getVariable() { result = global }

  IRFunction getIRFunction() { result = f }

  int getIndirectionIndex() { result = indirectionIndex }

  final predicate hasIndexInBlock(IRBlock block, int index) {
    exists(EnterFunctionInstruction enter |
      enter = f.getEnterFunctionInstruction() and
      block.getInstruction(index) = enter
    )
  }

  SourceVariable getSourceVariable() { sourceVariableIsGlobal(result, global, f, indirectionIndex) }

  final predicate hasIndexInBlock(IRBlock block, int index, SourceVariable sv) {
    this.hasIndexInBlock(block, index) and
    sv = this.getSourceVariable()
  }

  final Cpp::Location getLocation() { result = f.getLocation() }

  string toString() {
    if indirectionIndex = 0
    then result = global.toString()
    else result = global.toString() + " indirection"
  }

  Type getUnspecifiedType() { result = global.getUnspecifiedType() }
}

/**
 * Holds if `defOrUse1` is a definition which is first read by `use`,
 * or if `defOrUse1` is a use and `use` is a next subsequent use.
 *
 * In both cases, `use` can either be an explicit use written in the
 * source file, or it can be a phi node as computed by the SSA library.
 */
predicate adjacentDefRead(DefOrUse defOrUse1, UseOrPhi use) {
  exists(IRBlock bb1, int i1, SourceVariable v |
    defOrUse1.asDefOrUse().hasIndexInBlock(bb1, i1, v)
  |
    exists(IRBlock bb2, int i2, Definition def |
      adjacentDefRead(pragma[only_bind_into](def), pragma[only_bind_into](bb1),
        pragma[only_bind_into](i1), pragma[only_bind_into](bb2), pragma[only_bind_into](i2)) and
      def.getSourceVariable() = v and
      use.asDefOrUse().(UseImpl).hasIndexInBlock(bb2, i2, v)
    )
    or
    exists(PhiNode phi |
      lastRefRedef(_, bb1, i1, phi) and
      use.asPhi() = phi and
      phi.getSourceVariable() = pragma[only_bind_into](v)
    )
  )
}

/**
 * Holds if `defOrUse` should flow to the final use of the
 * global variable use represetned by `globalUse`.
 */
private predicate defOrUseToGlobalUse(DefOrUse defOrUse, GlobalUse globalUse) {
  exists(IRBlock bb1, int i1, IRBlock bb2, int i2, SourceVariable v |
    defOrUse.asDefOrUse().hasIndexInBlock(bb1, i1, v) and
    globalUse.hasIndexInBlock(bb2, i2, v) and
    adjacentDefRead(_, pragma[only_bind_into](bb1), pragma[only_bind_into](i1),
      pragma[only_bind_into](bb2), pragma[only_bind_into](i2))
  )
}

/**
 * Holds if `globalDef` represents the initial definition of a global variable that
 * flows to `useOrPhi`.
 */
private predicate globalDefToUse(GlobalDef globalDef, UseOrPhi useOrPhi) {
  exists(IRBlock bb1, int i1, IRBlock bb2, int i2, SourceVariable v |
    globalDef.hasIndexInBlock(bb1, i1, v) and
    adjacentDefRead(_, pragma[only_bind_into](bb1), pragma[only_bind_into](i1),
      pragma[only_bind_into](bb2), pragma[only_bind_into](i2)) and
    useOrPhi.asDefOrUse().hasIndexInBlock(bb2, i2, v)
  )
}

private predicate useToNode(UseOrPhi use, Node nodeTo) {
  exists(UseImpl useImpl |
    useImpl = use.asDefOrUse() and
    nodeHasOperand(nodeTo, useImpl.getOperand(), useImpl.getIndirectionIndex())
  )
  or
  nodeTo.(SsaPhiNode).getPhiNode() = use.asPhi()
}

pragma[noinline]
predicate outNodeHasAddressAndIndex(
  IndirectArgumentOutNode out, Operand address, int indirectionIndex
) {
  out.getAddressOperand() = address and
  out.getIndirectionIndex() = indirectionIndex
}

private predicate defToNode(Node nodeFrom, Def def, boolean uncertain) {
  (
    nodeHasOperand(nodeFrom, def.getValue().asOperand(), def.getIndirectionIndex())
    or
    nodeHasInstruction(nodeFrom, def.getValue().asInstruction(), def.getIndirectionIndex())
  ) and
  if def.isCertain() then uncertain = false else uncertain = true
}

/**
 * INTERNAL: Do not use.
 *
 * Holds if `nodeFrom` is the node that correspond to the definition or use `defOrUse`.
 */
predicate nodeToDefOrUse(Node nodeFrom, SsaDefOrUse defOrUse, boolean uncertain) {
  // Node -> Def
  defToNode(nodeFrom, defOrUse, uncertain)
  or
  // Node -> Use
  useToNode(defOrUse, nodeFrom) and
  uncertain = false
}

/**
 * Perform a single conversion-like step from `nFrom` to `nTo`. This relation
 * only holds when there is no use-use relation out of `nTo`.
 */
private predicate indirectConversionFlowStep(Node nFrom, Node nTo) {
  not exists(UseOrPhi defOrUse |
    nodeToDefOrUse(nTo, defOrUse, _) and
    adjacentDefRead(defOrUse, _)
  ) and
  exists(Operand op1, Operand op2, int indirectionIndex, Instruction instr |
    hasOperandAndIndex(nFrom, op1, pragma[only_bind_into](indirectionIndex)) and
    hasOperandAndIndex(nTo, op2, pragma[only_bind_into](indirectionIndex)) and
    instr = op2.getDef() and
    conversionFlow(op1, instr, _)
  )
}

/**
 * The reason for this predicate is a bit annoying:
 * We cannot mark a `PointerArithmeticInstruction` that computes an offset based on some SSA
 * variable `x` as a use of `x` since this creates taint-flow in the following example:
 * ```c
 * int x = array[source]
 * sink(*array)
 * ```
 * This is because `source` would flow from the operand of `PointerArithmeticInstruction` to the
 * result of the instruction, and into the `IndirectOperand` that represents the value of `*array`.
 * Then, via use-use flow, flow will arrive at `*array` in `sink(*array)`.
 *
 * So this predicate recurses back along conversions and `PointerArithmeticInstruction`s to find the
 * first use that has provides use-use flow, and uses that target as the target of the `nodeFrom`.
 */
private predicate adjustForPointerArith(Node nodeFrom, UseOrPhi use, boolean uncertain) {
  nodeFrom = any(PostUpdateNode pun).getPreUpdateNode() and
  exists(DefOrUse defOrUse, Node adjusted |
    indirectConversionFlowStep*(adjusted, nodeFrom) and
    nodeToDefOrUse(adjusted, defOrUse, uncertain) and
    adjacentDefRead(defOrUse, use)
  )
}

private predicate ssaFlowImpl(Node nodeFrom, Node nodeTo, boolean uncertain) {
  // `nodeFrom = any(PostUpdateNode pun).getPreUpdateNode()` is implied by adjustedForPointerArith.
  exists(UseOrPhi use |
    adjustForPointerArith(nodeFrom, use, uncertain) and
    useToNode(use, nodeTo)
  )
  or
  not nodeFrom = any(PostUpdateNode pun).getPreUpdateNode() and
  exists(DefOrUse defOrUse1, UseOrPhi use |
    nodeToDefOrUse(nodeFrom, defOrUse1, uncertain) and
    adjacentDefRead(defOrUse1, use) and
    useToNode(use, nodeTo)
  )
  or
  // Def/use to final value of global vairable
  exists(DefOrUse defOrUse, GlobalUse globalUse |
    nodeToDefOrUse(nodeFrom, defOrUse, uncertain) and
    defOrUseToGlobalUse(defOrUse, globalUse) and
    nodeTo.(FinalGlobalValue).getGlobalUse() = globalUse
  )
  or
  // Initial global variable value to a first use
  exists(GlobalDef globalDef, UseOrPhi use |
    nodeFrom.(InitialGlobalValue).getGlobalDef() = globalDef and
    globalDefToUse(globalDef, use) and
    useToNode(use, nodeTo) and
    uncertain = false
  )
}

/**
 * Holds if `def` is the corresponding definition of
 * the SSA library's `definition`.
 */
private predicate ssaDefinition(Def def, Definition definition) {
  exists(IRBlock block, int i, SourceVariable sv |
    def.hasIndexInBlock(block, i, sv) and
    definition.definesAt(sv, block, i)
  )
}

/** Gets a node that represents the prior definition of `node`. */
private Node getAPriorDefinition(Node node) {
  exists(Def def, Definition definition, Definition inp, Def input |
    defToNode(node, def, true) and
    ssaDefinition(def, definition) and
    uncertainWriteDefinitionInput(pragma[only_bind_into](definition), pragma[only_bind_into](inp)) and
    ssaDefinition(input, inp) and
    defToNode(result, input, _)
  )
}

/** Holds if there is def-use or use-use flow from `nodeFrom` to `nodeTo`. */
predicate ssaFlow(Node nodeFrom, Node nodeTo) {
  exists(Node nFrom, boolean uncertain |
    ssaFlowImpl(nFrom, nodeTo, uncertain) and
    if uncertain = true then nodeFrom = [nFrom, getAPriorDefinition(nFrom)] else nodeFrom = nFrom
  )
}

/**
 * Holds if `use` is a use of `sv` and is a next adjacent use of `phi` in
 * index `i1` in basic block `bb1`.
 *
 * This predicate exists to prevent an early join of `adjacentDefRead` with `definesAt`.
 */
pragma[nomagic]
private predicate fromPhiNodeToUse(PhiNode phi, SourceVariable sv, IRBlock bb1, int i1, UseOrPhi use) {
  exists(IRBlock bb2, int i2 |
    use.asDefOrUse().hasIndexInBlock(bb2, i2, sv) and
    adjacentDefRead(pragma[only_bind_into](phi), pragma[only_bind_into](bb1),
      pragma[only_bind_into](i1), pragma[only_bind_into](bb2), pragma[only_bind_into](i2))
  )
}

/** Holds if `nodeTo` receives flow from the phi node `nodeFrom`. */
predicate fromPhiNode(SsaPhiNode nodeFrom, Node nodeTo) {
  exists(PhiNode phi, SourceVariable sv, IRBlock bb1, int i1, UseOrPhi use |
    phi = nodeFrom.getPhiNode() and
    phi.definesAt(sv, bb1, i1) and
    useToNode(use, nodeTo)
  |
    fromPhiNodeToUse(phi, sv, bb1, i1, use)
    or
    exists(PhiNode phiTo |
      lastRefRedef(phi, _, _, phiTo) and
      nodeTo.(SsaPhiNode).getPhiNode() = phiTo
    )
  )
}

/**
 * Holds if there is a write at index `i` in basic block `bb` to variable `v` that's
 * subsequently read (as determined by the SSA pruning stage).
 */
private predicate variableWriteCand(IRBlock bb, int i, SourceVariable v) {
  exists(SsaInternals0::Def def, SsaInternals0::SourceVariable v0 |
    def.asDefOrUse().hasIndexInBlock(bb, i, v0) and
    v0 = v.getBaseVariable()
  )
}

private predicate sourceVariableIsGlobal(
  SourceVariable sv, Cpp::GlobalOrNamespaceVariable global, IRFunction func, int indirectionIndex
) {
  exists(IRVariable irVar, BaseIRVariable base |
    sourceVariableHasBaseAndIndex(sv, base, indirectionIndex) and
    irVar = base.getIRVariable() and
    irVar.getEnclosingIRFunction() = func and
    global = irVar.getAst()
  )
}

private module SsaInput implements SsaImplCommon::InputSig {
  import InputSigCommon
  import SourceVariables

  /**
   * Holds if the `i`'th write in block `bb` writes to the variable `v`.
   * `certain` is `true` if the write is guaranteed to overwrite the entire variable.
   */
  predicate variableWrite(IRBlock bb, int i, SourceVariable v, boolean certain) {
    DataFlowImplCommon::forceCachingInSameStage() and
    (
      variableWriteCand(bb, i, v) or
      sourceVariableIsGlobal(v, _, _, _)
    ) and
    exists(DefImpl def | def.hasIndexInBlock(bb, i, v) |
      if def.isCertain() then certain = true else certain = false
    )
    or
    exists(GlobalDef global |
      global.hasIndexInBlock(bb, i, v) and
      certain = true
    )
  }

  /**
   * Holds if the `i`'th read in block `bb` reads to the variable `v`.
   * `certain` is `true` if the read is guaranteed. For C++, this is always the case.
   */
  predicate variableRead(IRBlock bb, int i, SourceVariable v, boolean certain) {
    exists(UseImpl use | use.hasIndexInBlock(bb, i, v) |
      if use.isCertain() then certain = true else certain = false
    )
    or
    exists(GlobalUse global |
      global.hasIndexInBlock(bb, i, v) and
      certain = true
    )
  }
}

/**
 * The final SSA predicates used for dataflow purposes.
 */
cached
module SsaCached {
  /**
   * Holds if `def` is accessed at index `i1` in basic block `bb1` (either a read
   * or a write), `def` is read at index `i2` in basic block `bb2`, and there is a
   * path between them without any read of `def`.
   */
  cached
  predicate adjacentDefRead(Definition def, IRBlock bb1, int i1, IRBlock bb2, int i2) {
    SsaImpl::adjacentDefRead(def, bb1, i1, bb2, i2)
  }

  /**
   * Holds if the node at index `i` in `bb` is a last reference to SSA definition
   * `def`. The reference is last because it can reach another write `next`,
   * without passing through another read or write.
   */
  cached
  predicate lastRefRedef(Definition def, IRBlock bb, int i, Definition next) {
    SsaImpl::lastRefRedef(def, bb, i, next)
  }

  cached
  predicate uncertainWriteDefinitionInput(SsaImpl::UncertainWriteDefinition def, Definition inp) {
    SsaImpl::uncertainWriteDefinitionInput(def, inp)
  }
}

cached
private newtype TSsaDefOrUse =
  TDefOrUse(DefOrUseImpl defOrUse) {
    defOrUse instanceof UseImpl
    or
    // Like in the pruning stage, we only include definition that's live after the
    // write as the final definitions computed by SSA.
    exists(Definition def, SourceVariable sv, IRBlock bb, int i |
      def.definesAt(sv, bb, i) and
      defOrUse.(DefImpl).hasIndexInBlock(bb, i, sv)
    )
  } or
  TPhi(PhiNode phi)

abstract private class SsaDefOrUse extends TSsaDefOrUse {
  string toString() { none() }

  DefOrUseImpl asDefOrUse() { none() }

  PhiNode asPhi() { none() }

  abstract Location getLocation();
}

class DefOrUse extends TDefOrUse, SsaDefOrUse {
  DefOrUseImpl defOrUse;

  DefOrUse() { this = TDefOrUse(defOrUse) }

  final override DefOrUseImpl asDefOrUse() { result = defOrUse }

  final override Location getLocation() { result = defOrUse.getLocation() }

  final SourceVariable getSourceVariable() { result = defOrUse.getSourceVariable() }

  override string toString() { result = defOrUse.toString() }

  predicate hasIndexInBlock(IRBlock block, int index, SourceVariable sv) {
    defOrUse.hasIndexInBlock(block, index, sv)
  }
}

class Phi extends TPhi, SsaDefOrUse {
  PhiNode phi;

  Phi() { this = TPhi(phi) }

  final override PhiNode asPhi() { result = phi }

  final override Location getLocation() { result = phi.getBasicBlock().getLocation() }

  override string toString() { result = "Phi" }
}

class UseOrPhi extends SsaDefOrUse {
  UseOrPhi() {
    this.asDefOrUse() instanceof UseImpl
    or
    this instanceof Phi
  }

  final override Location getLocation() {
    result = this.asDefOrUse().getLocation() or result = this.(Phi).getLocation()
  }
}

class Def extends DefOrUse {
  override DefImpl defOrUse;

  Operand getAddressOperand() { result = defOrUse.getAddressOperand() }

  Instruction getAddress() { result = this.getAddressOperand().getDef() }

  /**
   * This predicate ensures that joins go from `defOrUse` to the result
   * instead of the other way around.
   */
  pragma[inline]
  int getIndirectionIndex() {
    pragma[only_bind_into](result) = pragma[only_bind_out](defOrUse).getIndirectionIndex()
  }

  Node0Impl getValue() { result = defOrUse.getValue() }

  predicate isCertain() { defOrUse.isCertain() }
}

private module SsaImpl = SsaImplCommon::Make<SsaInput>;

class PhiNode = SsaImpl::PhiNode;

class Definition = SsaImpl::Definition;

class UncertainWriteDefinition = SsaImpl::UncertainWriteDefinition;

import SsaCached
