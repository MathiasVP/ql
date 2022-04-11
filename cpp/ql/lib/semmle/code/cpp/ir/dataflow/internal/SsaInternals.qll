private import SsaImplCommon as Ssa
private import cpp as Cpp
private import semmle.code.cpp.ir.IR
private import DataFlowUtil
private import DataFlowImplCommon as DataFlowImplCommon
private import semmle.code.cpp.models.interfaces.Allocation as Alloc
private import semmle.code.cpp.models.interfaces.DataFlow as DataFlow
private import semmle.code.cpp.ir.implementation.raw.internal.SideEffects as SideEffects
private import semmle.code.cpp.ir.internal.IRCppLanguage
private import DataFlowPrivate

int getMaxIndirectionsForType(Type type) {
  result = SourceVariables::countIndirectionsForCppType(getTypeForGLValue(type))
}

private module SourceVariables {
  int countIndirectionsForCppType(LanguageType langType) {
    exists(Type type | langType.hasType(type, true) |
      result = 1 + countIndirections(type.getUnspecifiedType())
    )
    or
    exists(Type type | langType.hasType(type, false) |
      result = countIndirections(type.getUnspecifiedType())
    )
  }

  private int countIndirections(Type t) {
    result =
      1 +
        countIndirections([t.(Cpp::PointerType).getBaseType(), t.(Cpp::ReferenceType).getBaseType()])
    or
    not t instanceof Cpp::PointerType and
    not t instanceof Cpp::ReferenceType and
    result = 0
  }

  int getMaxIndirectionForIRVariable(IRVariable var) {
    exists(Type type, boolean isGLValue |
      var.getLanguageType().hasType(type, isGLValue) and
      if isGLValue = true
      then result = 1 + getMaxIndirectionsForType(type)
      else result = getMaxIndirectionsForType(type)
    )
  }

  newtype TBaseSourceVariable =
    TBaseIRVariable(IRVariable var) or
    TBaseCallVariable(CallInstruction call)

  abstract class BaseSourceVariable extends TBaseSourceVariable {
    abstract string toString();
  }

  class BaseIRVariable extends BaseSourceVariable, TBaseIRVariable {
    IRVariable var;

    IRVariable getIRVariable() { result = var }

    BaseIRVariable() { this = TBaseIRVariable(var) }

    override string toString() { result = var.toString() }
  }

  class BaseCallVariable extends BaseSourceVariable, TBaseCallVariable {
    CallInstruction call;

    BaseCallVariable() { this = TBaseCallVariable(call) }

    CallInstruction getCallInstruction() { result = call }

    override string toString() { result = call.toString() }
  }

  cached
  private newtype TSourceVariable =
    TSourceIRVariable(BaseIRVariable baseVar, int ind) {
      ind = [0 .. getMaxIndirectionForIRVariable(baseVar.getIRVariable())]
    } or
    TCallVariable(CallInstruction call, int ind) {
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
      result = ToStringUtils::stars().prefix(ind) + this.getIRVariable().toString()
    }
  }

  class CallVariable extends SourceVariable, TCallVariable {
    CallInstruction call;

    CallVariable() { this = TCallVariable(call, ind) }

    CallInstruction getCall() { result = call }

    override BaseCallVariable getBaseVariable() { result.getCallInstruction() = call }

    override string toString() { result = ToStringUtils::stars().prefix(ind) + call.toString() }
  }
}

import SourceVariables

cached
private newtype TDefOrUse =
  TNonCallDef(Operand address, int ind) { isNonCallDef(_, _, address, _, ind, _, _) } or
  TCallDef(Operand address, int ind) { isCallDef(_, address, _, ind, _, _) } or
  TUse(Operand operand, int ind) {
    isUse(_, operand, _, ind, _) and
    not isNonCallDef(_, _, operand, _, _, _, _)
  }

bindingset[isGLValue]
private CppType getThisType(Cpp::MemberFunction f, boolean isGLValue) {
  result.hasType(f.getTypeOfThis(), isGLValue)
}

CppType getResultLanguageType(Instruction i) {
  if i.(VariableAddressInstruction).getIRVariable() instanceof IRThisVariable
  then
    if i.isGLValue()
    then result = getThisType(i.getEnclosingFunction(), true)
    else result = getThisType(i.getEnclosingFunction(), false)
  else result = i.getResultLanguageType()
}

CppType getLanguageType(Operand operand) { result = getResultLanguageType(operand.getDef()) }

private predicate isCallDef(
  Instruction instr, Operand address, Instruction base, int ind, int index,
  boolean addressDependsOnField
) {
  exists(int ind0, CallInstruction call, CppType addressType, int mAddress, int argumentIndex |
    if argumentIndex = -1
    then not call.getStaticCallTarget() instanceof Cpp::ConstMemberFunction
    else not SideEffects::isConstPointerLike(any(Type t | addressType.hasType(t, _)))
  |
    call = instr and
    address = call.getArgumentOperand(argumentIndex) and
    isDefImpl(address, base, ind0, addressDependsOnField, _) and
    addressType = getLanguageType(address) and
    mAddress = countIndirectionsForCppType(addressType) and
    ind = [ind0 + 1 .. mAddress + ind0] and
    index = ind - (ind0 + 1)
  )
}

abstract private class DefOrUse extends TDefOrUse {
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

  abstract int getIndex();

  abstract Instruction getBase();

  final BaseSourceVariable getBaseSourceVariable() {
    exists(IRVariable var |
      result.(BaseIRVariable).getIRVariable() = var and
      instructionHasIRVariable(this.getBase(), var)
    )
    or
    result.(BaseCallVariable).getCallInstruction() = this.getBase()
  }

  /** Gets the variable that is defined or used. */
  final SourceVariable getSourceVariable() {
    exists(BaseSourceVariable v, int ind |
      sourceVariableHasBaseAndIndex(result, v, ind) and
      defOrUseHasSourceVariable(this, v, ind)
    )
  }
}

private predicate defOrUseHasSourceVariable(DefOrUse defOrUse, BaseSourceVariable bv, int ind) {
  defHasSourceVariable(defOrUse, bv, ind)
  or
  useHasSourceVariable(defOrUse, bv, ind)
}

pragma[noinline]
private predicate defHasSourceVariable(Def def, BaseSourceVariable bv, int ind) {
  bv = def.getBaseSourceVariable() and
  ind = def.getIndirection()
}

pragma[noinline]
private predicate useHasSourceVariable(Use use, BaseSourceVariable bv, int ind) {
  bv = use.getBaseSourceVariable() and
  ind = use.getIndirection()
}

pragma[noinline]
private predicate sourceVariableHasBaseAndIndex(SourceVariable v, BaseSourceVariable bv, int ind) {
  v.getBaseVariable() = bv and
  v.getIndirection() = ind
}

abstract class Def extends DefOrUse {
  abstract predicate isCertain();

  abstract int getIndirection();

  abstract Operand getAddressOperand();

  final Instruction getAddress() { result = this.getAddressOperand().getDef() }

  abstract Instruction getDefiningInstruction();

  abstract predicate addressDependsOnField();
}

class NonCallDef extends Def, TNonCallDef {
  Operand address;
  int ind;

  NonCallDef() { this = TNonCallDef(address, ind) }

  override Instruction getBase() { isNonCallDef(_, _, address, result, _, _, _) }

  override Operand getAddressOperand() { result = address }

  override int getIndirection() { result = ind }

  override int getIndex() { isNonCallDef(_, _, address, _, ind, result, _) }

  override Instruction getDefiningInstruction() { isNonCallDef(_, result, address, _, _, _, _) }

  override string toString() {
    result = ToStringUtils::stars().prefix(ind) + this.getDefiningInstruction().toString()
  }

  override IRBlock getBlock() { result = this.getDefiningInstruction().getBlock() }

  override Cpp::Location getLocation() { result = this.getDefiningInstruction().getLocation() }

  final override predicate hasIndexInBlock(IRBlock block, int index) {
    this.getDefiningInstruction() = block.getInstruction(index)
  }

  override predicate isCertain() { isNonCallDef(true, _, address, _, ind, _, _) }

  override predicate addressDependsOnField() { isNonCallDef(_, _, address, _, ind, _, true) }
}

class CallDef extends Def, TCallDef {
  Operand address;
  int ind;

  CallDef() { this = TCallDef(address, ind) }

  override int getIndex() { isCallDef(_, address, _, ind, result, _) }

  override Instruction getBase() { isCallDef(_, address, result, _, _, _) }

  override Operand getAddressOperand() { result = address }

  override Instruction getDefiningInstruction() { isCallDef(result, address, _, _, _, _) }

  override int getIndirection() { result = ind }

  override string toString() {
    result =
      ToStringUtils::stars().prefix(this.getIndirection()) +
        this.getDefiningInstruction().toString() + " (synthetic)"
  }

  override IRBlock getBlock() { result = this.getDefiningInstruction().getBlock() }

  override Cpp::Location getLocation() { result = address.getLocation() }

  final override predicate hasIndexInBlock(IRBlock block, int index) {
    this.getDefiningInstruction() = block.getInstruction(index)
  }

  override predicate isCertain() { none() }

  override predicate addressDependsOnField() { isCallDef(_, address, _, _, _, true) }
}

class Use extends DefOrUse, TUse {
  Operand operand;
  int ind;

  Use() { this = TUse(operand, ind) }

  Operand getOperand() { result = operand }

  override string toString() { result = ToStringUtils::stars().prefix(ind) + operand.toString() }

  final override predicate hasIndexInBlock(IRBlock block, int index) {
    operand.getUse() = block.getInstruction(index)
  }

  final override IRBlock getBlock() { result = operand.getUse().getBlock() }

  final override Cpp::Location getLocation() { result = operand.getLocation() }

  final int getIndirection() { result = ind }

  override int getIndex() { isUse(_, operand, _, ind, result) }

  override Instruction getBase() { isUse(_, operand, result, ind, _) }
}

private predicate isUse(boolean certain, Operand op, Instruction base, int ind, int index) {
  not ignoreOperand(op) and
  certain = true and
  exists(LanguageType type, int m, int ind0 |
    type = getLanguageType(op) and
    m = countIndirectionsForCppType(type) and
    isUseImpl(op, base, ind0) and
    ind = [ind0 .. m + ind0] and
    index = ind - ind0
  )
}

private predicate isNonCallDef(
  boolean certain, Instruction instr, Operand address, Instruction base, int ind, int index,
  boolean addressDependsOnField
) {
  exists(int ind0, CppType type, int m |
    address =
      [
        instr.(StoreInstruction).getDestinationAddressOperand(),
        instr.(InitializeParameterInstruction).getAnOperand(),
        instr.(InitializeDynamicAllocationInstruction).getAllocationAddressOperand()
      ] and
    isDefImpl(address, base, ind0, addressDependsOnField, certain) and
    type = getLanguageType(address) and
    m = countIndirectionsForCppType(type) and
    ind = [ind0 + 1 .. ind0 + m] and
    index = ind - (ind0 + 1)
  )
}

private predicate isSourceVariableBase(Instruction i) {
  i instanceof VariableAddressInstruction or i instanceof CallInstruction
}

private predicate isPointerOrField(Instruction instr) {
  instr instanceof PointerArithmeticInstruction
  or
  instr instanceof FieldAddressInstruction
}

private predicate isDefImpl(
  Operand address, Instruction base, int ind, boolean addressDependsOnField, boolean certain
) {
  ind = 0 and
  address.getDef() = base and
  isSourceVariableBase(base) and
  addressDependsOnField = false and
  certain = true
  or
  exists(Operand mid, boolean isField0, boolean isField1, boolean certain0 |
    isDefImpl(mid, base, ind, isField0, certain0) and
    conversionFlow(mid, address, isField1) and
    addressDependsOnField = isField0.booleanOr(isField1) and
    if isPointerOrField(address.getDef()) then certain = false else certain = certain0
  )
  or
  exists(int ind0 |
    isDefImpl(address.getDef().(LoadInstruction).getSourceAddressOperand(), base, ind0,
      addressDependsOnField, certain)
    or
    isDefImpl(address.getDef().(InitializeParameterInstruction).getAnOperand(), base, ind0,
      addressDependsOnField, certain)
  |
    if addressDependsOnField = true then ind = ind0 else ind0 = ind - 1
  )
}

private predicate isUseImpl(Operand operand, Instruction base, int ind) {
  ind = 0 and
  operand.getDef() = base and
  isSourceVariableBase(base)
  or
  exists(Operand mid |
    isUseImpl(mid, base, ind) and
    conversionFlowStepExcludeFields(mid, operand)
  )
  or
  exists(int ind0 |
    isUseImpl(operand.getDef().(LoadInstruction).getSourceAddressOperand(), base, ind0)
    or
    isUseImpl(operand.getDef().(InitializeParameterInstruction).getAnOperand(), base, ind0)
  |
    ind0 = ind - 1
  )
}

pragma[noinline]
private predicate instructionHasIRVariable(VariableAddressInstruction vai, IRVariable var) {
  vai.getIRVariable() = var
}

private predicate adjacentDefRead0(DefOrUse defOrUse1, DefOrUse defOrUse2) {
  exists(IRBlock bb1, int i1, IRBlock bb2, int i2, SourceVariable v |
    defOrUse2.hasIndexInBlock(bb2, i2, v) and
    defOrUse1.hasIndexInBlock(bb1, i1, v) and
    adjacentDefRead(_, pragma[only_bind_into](bb1), pragma[only_bind_into](i1),
      pragma[only_bind_into](bb2), pragma[only_bind_into](i2))
  )
}

private predicate adjacentDefReadStep(Def def, DefOrUse defOrUse) {
  adjacentDefRead0(def, defOrUse)
}

cached
predicate adjacentDefRead(DefOrUse defOrUse1, Use use) {
  exists(DefOrUse mid | adjacentDefRead0(defOrUse1, mid) |
    adjacentDefReadStep+(mid, use) // implies `mid instanceof Def`
    or
    mid = use // implies `mid instanceof Use`
  )
}

private predicate useToNode(Use use, Node nodeTo) {
  use.getIndex() = 0 and
  nodeTo.asInstruction() = use.getOperand().getDef()
  or
  exists(int index |
    index = use.getIndex() and
    index > 0 and
    hasOperandAndIndex(nodeTo, use.getOperand(), index)
  )
}

private predicate nodeToNonCallDef(Node nodeFrom, NonCallDef def) {
  def.getIndex() = 0 and
  def.getDefiningInstruction() = nodeFrom.asInstruction()
  or
  // implies def.getIndex() > 0
  hasInstructionAndIndex(nodeFrom, def.getDefiningInstruction(), def.getIndex())
}

private predicate outNodeToCallDef(IndirectArgumentOutNode nodeFrom, CallDef def) {
  nodeFrom.getDef() = def
}

predicate nodeToDefOrUse(Node nodeFrom, DefOrUse defOrUse) {
  // Node -> Def
  nodeToNonCallDef(nodeFrom, defOrUse)
  or
  outNodeToCallDef(nodeFrom, defOrUse)
  or
  // Node -> Use
  useToNode(defOrUse, nodeFrom)
}

predicate defUseFlow(Node nodeFrom, Node nodeTo) {
  exists(DefOrUse defOrUse1 |
    not defOrUse1.(Def).addressDependsOnField() and
    nodeToDefOrUse(nodeFrom, defOrUse1)
  |
    exists(Use use |
      adjacentDefRead(defOrUse1, use) and
      useToNode(use, nodeTo)
    )
    or
    exists(PhiNode phi, int i, IRBlock block, Definition def |
      def.definesAt(_, block, i) and
      defOrUse1.hasIndexInBlock(block, i) and
      phi.getSourceVariable() = defOrUse1.getSourceVariable() and
      phiHasInputFromBlock(phi, def, _) and
      nodeTo.(SsaPhiNode).getPhiNode() = phi
    )
  )
}

predicate postNodeDefUseFlow(PostFieldUpdateNode pfun, Node nodeTo) {
  exists(Def def, Use use |
    not isQualifierFor(any(FieldAddress fa), pfun.getFieldAddress()) and
    def = pfun.getDef() and
    adjacentDefRead(def, use) and
    useToNode(use, nodeTo)
  )
}

predicate fromPhiNode(SsaPhiNode nodeFrom, Node nodeTo) {
  exists(Use use, IRBlock bb2, int i2, PhiNode phi, SourceVariable v |
    use.hasIndexInBlock(bb2, i2, v) and
    phi = nodeFrom.getPhiNode() and
    phi.getSourceVariable() = v and
    adjacentDefRead(phi, _, -1, bb2, i2) and
    useToNode(use, nodeTo)
  )
}

predicate toPhiNode(Node nodeFrom, SsaPhiNode nodeTo) {
  exists(Definition input, IRBlock block, int index, Def def, SourceVariable v |
    nodeToDefOrUse(nodeFrom, def) and
    input.definesAt(v, block, index) and
    def.hasIndexInBlock(block, index, v) and
    nodeTo.hasInputAtRankInBlock(block, index, input)
  )
  or
  nodeTo.hasInputAtRankInBlock(_, _, nodeFrom.(SsaPhiNode).getPhiNode())
}

/**
 * Holds if the `i`'th write in block `bb` writes to the variable `v`.
 * `certain` is `true` if the write is guaranteed to overwrite the entire variable.
 */
predicate variableWrite(IRBlock bb, int i, SourceVariable v, boolean certain) {
  DataFlowImplCommon::forceCachingInSameStage() and
  exists(Def def |
    def.hasIndexInBlock(bb, i, v) and
    (if def.isCertain() then certain = true else certain = false)
  )
}

/**
 * Holds if the `i`'th read in block `bb` reads to the variable `v`.
 * `certain` is `true` if the read is guaranteed. For C++, this is always the case.
 */
predicate variableRead(IRBlock bb, int i, SourceVariable v, boolean certain) {
  exists(Use use |
    use.hasIndexInBlock(bb, i, v) and
    certain = true
  )
  or
  exists(Def def |
    def.hasIndexInBlock(bb, i, v) and
    not def.isCertain() and
    certain = false
  )
}

cached
module SsaCached {
  cached
  predicate phiHasInputFromBlock(PhiNode phi, Definition inp, IRBlock bb) {
    Ssa::phiHasInputFromBlock(phi, inp, bb)
  }

  cached
  predicate adjacentDefRead(Definition def, IRBlock bb1, int i1, IRBlock bb2, int i2) {
    Ssa::adjacentDefRead(def, bb1, i1, bb2, i2)
  }
}

import SsaCached

class PhiNode = Ssa::PhiNode;

class Definition = Ssa::Definition;
