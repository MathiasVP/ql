import SsaImplCommon
private import cpp as Cpp
private import semmle.code.cpp.ir.IR
private import DataFlowUtil
private import DataFlowImplCommon as DataFlowImplCommon
private import semmle.code.cpp.models.interfaces.Allocation as Alloc
private import semmle.code.cpp.models.interfaces.DataFlow as DataFlow
private import semmle.code.cpp.ir.internal.IRCppLanguage

int getMaxIndirectionsForType(Type type) {
  result = SourceVariables::countIndirectionsForCppType(getTypeForGLValue(type))
}

private module SourceVariables {
  int countIndirectionsForCppType(LanguageType langType) {
    exists(Type type | langType.hasType(type, true) | result = 1 + countIndirections(type))
    or
    exists(Type type | langType.hasType(type, false) | result = countIndirections(type))
  }

  private int countIndirections(Type t) {
    result = 1 + countIndirections(t.(Cpp::PointerType).getBaseType())
    or
    not t instanceof Cpp::PointerType and
    result = 0
  }

  int getMaxIndirection(IRVariable var) {
    exists(Type type |
      var.getLanguageType().hasType(type, _) and
      result = getMaxIndirectionsForType(type)
    )
  }

  cached
  private newtype TSourceVariable =
    TSourceIRVariable(IRVariable var, int ind) {
      exists(Type type |
        var.getLanguageType().hasType(type, _) and
        ind = [0 .. getMaxIndirection(var)]
      )
    } or
    TAllocation(CallInstruction call, int ind) {
      call.getStaticCallTarget() instanceof Alloc::OperatorNewAllocationFunction and
      ind = [0, 1]
    }

  abstract class SourceVariable extends TSourceVariable {
    int ind;

    bindingset[ind]
    SourceVariable() { any() }

    abstract string toString();

    int getIndirection() { result = ind }

    abstract SourceVariable incrementIndirection();

    final SourceVariable decrementIndirection() { result.incrementIndirection() = this }
  }

  class SourceIRVariable extends SourceVariable, TSourceIRVariable {
    IRVariable var;

    SourceIRVariable() { this = TSourceIRVariable(var, ind) }

    IRVariable getIRVariable() { result = var }

    override SourceIRVariable incrementIndirection() {
      result.getIRVariable() = var and result.getIndirection() = ind + 1
    }

    override string toString() {
      result = "*******************".prefix(ind) + this.getIRVariable().toString()
    }
  }

  class Allocation extends SourceVariable, TAllocation {
    CallInstruction call;

    Allocation() { this = TAllocation(call, ind) }

    CallInstruction getCall() { result = call }

    override Allocation incrementIndirection() {
      result.getCall() = call and result.getIndirection() = ind + 1
    }

    override string toString() { result = "*******************".prefix(ind) + call.toString() }
  }
}

import SourceVariables

module ExtendedBasicBlock {
  cached
  newtype TSSAInstruction =
    TSSAIRInstruction(Instruction i) {
      // We don't want to use the IR's phi instructions for dataflow SSA
      not i instanceof PhiInstruction and
      // We use the initialize instruction to initialize all the indirections
      not i instanceof InitializeIndirectionInstruction and
      not exists(TSSADefInstruction(i, _, _, _))
    } or
    TSSADefInstruction(Instruction store, Instruction base, int ind, int index) {
      exists(int ind0 |
        isExplicitWrite(_, store, base, ind0) and
        // A def of a is also a def of *^n a is also a use of *^(n-1) a, .., &a
        ind = getSourceVariable(base, 0).incrementIndirection*().getIndirection() and
        // Only the non-zero indices are actually useful to us. The other ones are for making sure that the correct variables are live.
        index = ind - ind0
      )
    }

  abstract class SSAInstruction extends TSSAInstruction {
    Instruction instr;

    abstract string toString();

    abstract int getIndex();

    abstract SSAOperand getAnOperand();

    Instruction getInstruction() { result = instr }

    IRBlock getBlock() { result = instr.getBlock() }

    Location getLocation() { result = instr.getLocation() }

    SourceVariable getSourceVariable() { none() } // overriden in subclasses

    Function getEnclosingFunction() { result = instr.getEnclosingFunction() }

    // TODO: This isn't quite right. It depends on which indirection it is.
    IRType getResultIRType() { result = instr.getResultIRType() }

    Expr getConvertedResultExpression() { none() } // overriden in subclasses

    Expr getUnconvertedResultExpression() { none() } // overriden in subclasses
  }

  private class SSAIRInstruction extends SSAInstruction, TSSAIRInstruction {
    SSAIRInstruction() { this = TSSAIRInstruction(instr) }

    override int getIndex() { result = 0 }

    override string toString() { result = instr.toString() }

    override SSAOperand getAnOperand() {
      result.(SSAIROperand).getOperand() = instr.getAnOperand()
      or
      exists(Operand operand |
        // Pick an operand of the instruction we're wrapping
        operand = instr.getAnOperand() and
        // And pick a `UseOperand`
        operand = result.(SSAUseOperand).getOperand()
      )
    }

    override Expr getConvertedResultExpression() { result = instr.getConvertedResultExpression() }

    override Expr getUnconvertedResultExpression() {
      result = instr.getUnconvertedResultExpression()
    }
  }

  class SSADefInstruction extends SSAInstruction, TSSADefInstruction {
    Instruction base;
    int ind;
    int index;

    SSADefInstruction() { this = TSSADefInstruction(instr, base, ind, index) }

    override int getIndex() { result = index }

    override string toString() { result = instr.toString() + ": [" + index + ", " + getSourceVariable().toString() + "]" }

    override SourceVariable getSourceVariable() { result = getSourceVariable(base, ind) }

    // SourceVariable getActualSourceVariable() {
    //   exists(int ind0 |
    //     isExplicitWrite(_, instr, base, ind0) and
    //     result = getSourceVariable(base, ind0)
    //   )
    // }
    // private int getIndex() { isExplicitWrite(_, instr, base, ind - result) }
    override SSAOperand getAnOperand() {
      result.(SSAIROperand).getOperand() = instr.getAnOperand()
      or
      exists(Operand operand |
        // Pick an operand of the instruction we're wrapping
        operand = instr.getAnOperand() and
        // And pick a `UseOperand`
        operand = result.(SSAUseOperand).getOperand()
      )
    }
  }

  cached
  newtype TSSAOperand =
    TSSAIROperand(Operand op) { not exists(TSSAUseOperand(op, _, _, _)) } or
    TSSAUseOperand(Operand op, Instruction base, int ind, int index) {
      exists(int ind0 |
        isExplicitUse(_, op.getDef(), base, ind0) and
        ind = getSourceVariable(base, ind0).incrementIndirection*().getIndirection() and
        index = ind - ind0
      )
    }

  abstract class SSAOperand extends TSSAOperand {
    Operand op;

    final Operand getOperand() { result = op }

    abstract string toString();

    predicate isSynthesized() { none() } // overriden in subclasses

    abstract int getIndex();

    final Location getLocation() { result = op.getLocation() }

    SourceVariable getSourceVariable() { none() } // overridden in subclasses

    IRBlock getBlock() { result = op.getDef().getBlock() }

    SSAInstruction getUse() { result.getAnOperand() = this }

    IRType getIRType() { result = op.getIRType() }
  }

  class SSAIROperand extends SSAOperand, TSSAIROperand {
    SSAIROperand() { this = TSSAIROperand(op) }

    override string toString() { result = op.toString() }

    override int getIndex() { result = 0 }
  }

  class SSAUseOperand extends SSAOperand, TSSAUseOperand {
    Instruction base;
    int ind;
    int index;

    SSAUseOperand() { this = TSSAUseOperand(op, base, ind, index) }

    override predicate isSynthesized() {
      not this.getSourceVariable() = this.getActualSourceVariable()
    }

    override int getIndex() { result = index }

    override string toString() {
      result =
        op.getDumpString() + " @ " + op.getUse().getResultId() + ": [" + index + ", " +
          this.getSourceVariable() + "]"
    }

    override SourceVariable getSourceVariable() { result = getSourceVariable(base, ind) }

    SourceVariable getActualSourceVariable() {
      exists(int ind0 |
        isExplicitUse(_, op.getDef(), base, ind0) and
        result = getSourceVariable(base, ind0)
      )
    }
  }

  private SSADefInstruction getFirstSSADefInstruction(Instruction instr) {
    result = min(int index | | TSSADefInstruction(instr, _, _, index) order by index)
  }

  private SSADefInstruction getLastSSADefInstruction(Instruction instr) {
    result = max(int index | | TSSADefInstruction(instr, _, _, index) order by index)
  }

  private predicate hasIndexInBlock(Instruction instr, IRBlock block, int index) {
    instr =
      rank[index](Instruction i, int idx |
        exists(getFirstInstruction(i)) and block.getInstruction(idx) = i
      |
        i order by idx
      )
  }

  private predicate adjacentInBlock(SSAInstruction instr1, SSAInstruction instr2) {
    exists(IRBlock block, Instruction i1, int index, Instruction i2 |
      instr1 = getLastInstruction(i1) and
      hasIndexInBlock(i1, block, index) and
      hasIndexInBlock(i2, block, index + 1) and
      instr2 = getFirstInstruction(i2)
    )
    or
    exists(Instruction i, Instruction base, int ind1, int ind2, int index |
      instr1 = TSSADefInstruction(i, base, ind1, index) and
      instr2 = TSSADefInstruction(i, base, ind2, index + 1)
    )
  }

  private predicate startsBasicBlock(SSAInstruction instr) { not adjacentInBlock(_, instr) }

  private SSAInstruction getInstructionFromFirst(SSAInstruction first, int index) =
    shortestDistances(startsBasicBlock/1, adjacentInBlock/2)(first, result, index)

  private SSAInstruction getFirstInstruction(Instruction instr) {
    result = TSSAIRInstruction(instr)
    or
    result = getFirstSSADefInstruction(instr)
  }

  private SSAInstruction getLastInstruction(Instruction instr) {
    result = TSSAIRInstruction(instr)
    or
    result = getLastSSADefInstruction(instr)
  }

  /** Holds if `i` is the `index`th instruction in `block`. */
  SSAInstruction getInstruction(IRBlock block, int index) {
    result = getInstructionFromFirst(getFirstInstruction(block.getFirstInstruction()), index)
  }
}

import ExtendedBasicBlock

cached
private newtype TDefOrUse =
  TExplicitDef(SSADefInstruction store) or
  TExplicitUseOperand(SSAUseOperand operand)

abstract private class DefOrUse extends TDefOrUse {
  /** Gets a textual representation of this element. */
  abstract string toString();

  /** Gets the block of this definition or use. */
  abstract IRBlock getBlock();

  /** Gets the variable that is defined or used. */
  abstract SourceVariable getSourceVariable();

  // abstract SourceVariable getActualSourceVariable();
  // predicate isActual() { this.getSourceVariable() = this.getActualSourceVariable() }
  /** Holds if this definition or use has index `index` in block `block`. */
  abstract predicate hasIndexInBlock(IRBlock block, int index);

  /** Gets the location of this element. */
  abstract Cpp::Location getLocation();
}

class Def extends DefOrUse {
  Def() { this = TExplicitDef(_) }

  override string toString() { none() } // overriden in subclasses

  override IRBlock getBlock() { none() } // overriden in subclasses

  override SourceVariable getSourceVariable() { none() } // overriden in subclasses

  // override SourceVariable getActualSourceVariable() { none() } // overriden in subclasses
  override predicate hasIndexInBlock(IRBlock block, int index) { none() } // overriden in subclasses

  override Cpp::Location getLocation() { none() } // overriden in subclasses

  /** Holds if this definition is guaranteed to happen. */
  predicate isCertain() { none() } // overriden in subclasses
}

private class ExplicitDef extends Def, TExplicitDef {
  SSADefInstruction instr;

  ExplicitDef() { this = TExplicitDef(instr) }

  final override SourceVariable getSourceVariable() { result = instr.getSourceVariable() }

  SSADefInstruction getInstruction() { result = instr }

  override string toString() { result = instr.toString() }

  // override SourceVariable getActualSourceVariable() { result = instr.getActualSourceVariable() }
  override IRBlock getBlock() { result = this.getInstruction().getBlock() }

  override Cpp::Location getLocation() { result = instr.getLocation() }

  final override predicate hasIndexInBlock(IRBlock block, int index) {
    instr = getInstruction(block, index)
  }

  override predicate isCertain() { isExplicitWrite(true, instr.getInstruction(), _, _) }
}

class Use extends DefOrUse {
  Use() { this = TExplicitUseOperand(_) }

  override string toString() { none() } // overriden in subclasses

  override IRBlock getBlock() { none() } // overriden in subclasses

  override SourceVariable getSourceVariable() { none() } // overriden in subclasses

  // override SourceVariable getActualSourceVariable() { none() } // overriden in subclasses
  override predicate hasIndexInBlock(IRBlock block, int index) { none() } // overriden in subclasses

  override Cpp::Location getLocation() { none() } // overriden in subclasses
}

private class UseOperand extends Use, TExplicitUseOperand {
  SSAUseOperand operand;

  UseOperand() { this = TExplicitUseOperand(operand) }

  // override SourceVariable getActualSourceVariable() { result = operand.getActualSourceVariable() }
  SSAUseOperand getSSAOperand() { result = operand }

  override string toString() { result = operand.toString() }

  // TODO: This only holds for 1 of the operands in the deref chain. Is that bad?
  final override predicate hasIndexInBlock(IRBlock block, int index) {
    exists(SSAInstruction use |
      use = ExtendedBasicBlock::getInstruction(block, index) and
      operand = use.getAnOperand()
    )
  }

  override IRBlock getBlock() { result = operand.getBlock() }

  override Cpp::Location getLocation() { result = operand.getLocation() }

  final override SourceVariable getSourceVariable() { result = operand.getSourceVariable() }
}

predicate conversionFlow(Instruction iFrom, Instruction iTo, boolean hasFieldOffset) {
  hasFieldOffset = false and
  (
    iTo.(CopyValueInstruction).getSourceValue() = iFrom
    or
    iTo.(ConvertInstruction).getUnary() = iFrom
    or
    iTo.(CheckedConvertOrNullInstruction).getUnary() = iFrom
    or
    iTo.(InheritanceConversionInstruction).getUnary() = iFrom
    or
    iTo.(PointerArithmeticInstruction).getLeft() = iFrom
  )
  or
  exists(FieldAddressInstruction fai |
    iTo = fai and
    iFrom = fai.getObjectAddress() and
    hasFieldOffset = true
  )
}

cached
predicate isExplicitUse(boolean certain, Instruction instr, Instruction base, int ind) {
  certain = true and
  isExplicitDefOrUseImpl(instr, base, ind, _) and
  not isExplicitWrite(_, instr, _, _)
}

cached
predicate isExplicitWrite(boolean certain, Instruction instr, Instruction base, int ind) {
  certain = true and // TODO: Should we actually use certain for something?
  exists(Instruction address |
    address =
      [
        instr.(StoreInstruction).getDestinationAddress(),
        instr.(ReturnIndirectionInstruction).getSourceAddress(),
        instr.(WriteSideEffectInstruction).getDestinationAddress(),
        instr.(InitializeParameterInstruction).getAnOperand().getDef(),
        instr.(InitializeDynamicAllocationInstruction).getAllocationAddress()
      ] and
    isExplicitDefOrUseImpl(address, base, ind - 1, _)
  )
}

private predicate isExplicitDefOrUseImpl(
  Instruction instr, Instruction base, int ind, boolean isField
) {
  ind = 0 and
  instr = base and
  exists(getSourceVariable(instr, ind)) and
  isField = false
  or
  exists(Instruction mid, boolean isField0, boolean isField1 |
    isExplicitDefOrUseImpl(mid, base, ind, isField0) and
    conversionFlow(mid, instr, isField1) and
    isField = isField0.booleanOr(isField1)
  )
  or
  exists(int ind0 |
    isExplicitDefOrUseImpl(instr.(LoadInstruction).getSourceAddress(), base, ind0, isField)
  |
    if isField = true then ind = ind0 else ind0 = ind - 1
  )
}

/**
 * Gets the destination address of `instr` if it is a `StoreInstruction` or
 * a `WriteSideEffectInstruction`.
 */
Instruction getDestinationAddress(Instruction instr) {
  result =
    [
      instr.(StoreInstruction).getDestinationAddress(),
      instr.(WriteSideEffectInstruction).getDestinationAddress()
    ]
}

/** Gets the source address of `instr` if it is an instruction that behaves like a `LoadInstruction`. */
Instruction getSourceAddress(Instruction instr) { result = getSourceAddressOperand(instr).getDef() }

/**
 * Gets the operand that represents the source address of `instr` if it is an
 * instruction that behaves like a `LoadInstruction`.
 */
Operand getSourceAddressOperand(Instruction instr) {
  result =
    [
      instr.(LoadInstruction).getSourceAddressOperand(),
      instr.(ReadSideEffectInstruction).getArgumentOperand()
    ]
}

/**
 * Gets the source address of `node` if it's an instruction or operand that
 * behaves like a `LoadInstruction`.
 */
Instruction getSourceAddressFromNode(Node node) {
  result = getSourceAddress(node.asInstruction())
  or
  result = getSourceAddress(node.asOperand().(SideEffectOperand).getUse())
}

/** Gets the source value of `instr` if it's an instruction that behaves like a `LoadInstruction`. */
Instruction getSourceValue(Instruction instr) { result = getSourceValueOperand(instr).getDef() }

/**
 * Gets the operand that represents the source value of `instr` if it's an instruction
 * that behaves like a `LoadInstruction`.
 */
Operand getSourceValueOperand(Instruction instr) {
  result = instr.(LoadInstruction).getSourceValueOperand()
  or
  result = instr.(ReadSideEffectInstruction).getSideEffectOperand()
}

pragma[noinline]
private predicate sourceVariableHasIRVariable(SourceIRVariable sourceVariable, IRVariable var) {
  sourceVariable.getIRVariable() = var
}

pragma[noinline]
private predicate instructionHasIRVariable(VariableAddressInstruction vai, IRVariable var) {
  vai.getIRVariable() = var
}

bindingset[ind]
SourceVariable getSourceVariable(Instruction instr, int ind) {
  result.getIndirection() = pragma[only_bind_into](pragma[only_bind_out](ind)) and
  (
    exists(IRVariable var |
      sourceVariableHasIRVariable(result, var) and
      instructionHasIRVariable(instr, var)
    )
    or
    instr = result.(Allocation).getCall()
  )
}

cached
predicate adjacentDefRead(DefOrUse defOrUse, Use use) {
  exists(IRBlock bb1, int i1, IRBlock bb2, int i2, Definition def, SourceVariable v |
    defOrUse.hasIndexInBlock(bb1, i1) and
    use.hasIndexInBlock(bb2, i2) and
    adjacentDefRead(def, bb1, i1, bb2, i2) and
    def.definesAt(v, _, _) and
    v = use.getSourceVariable() and
    v = defOrUse.getSourceVariable()
  )
}

SSAOperand decrementUseOperand(SSAOperand operand) {
  result.getOperand() = operand.getOperand() and
  result.getSourceVariable().decrementIndirection() = operand.getSourceVariable()
}

predicate defUseFlow(Node nodeFrom, Node nodeTo) {
  exists(DefOrUse defOrUse, Use use | adjacentDefRead(defOrUse, use) |
    (
      defOrUse.(ExplicitDef).getInstruction() = nodeFrom.(InstructionNode).getSSAIntruction()
      or
      // TODO: Also handle flow to ReturnIndirectionNodes here?
      if defOrUse.(UseOperand).getSSAOperand().getUse().getInstruction() instanceof LoadInstruction
      then
        decrementUseOperand(nodeFrom.(OperandNode).getSSAOperand()) =
          defOrUse.(UseOperand).getSSAOperand()
      else defOrUse.(UseOperand).getSSAOperand() = nodeFrom.(OperandNode).getSSAOperand()
    ) and
    use.(UseOperand).getSSAOperand() = nodeTo.(OperandNode).getSSAOperand()
  )
}

cached
private module Cached {
  private predicate fromPhiNode(SsaPhiNode nodeFrom, Node nodeTo) {
    exists(Use use, IRBlock bb2, int i2 |
      use.hasIndexInBlock(bb2, i2) and
      adjacentDefRead(nodeFrom.getPhiNode(), _, -1, bb2, i2)
    |
      nodeTo.asOperand() = use.(UseOperand).getSSAOperand().getOperand()
    )
  }

  private predicate toPhiNode(Node nodeFrom, SsaPhiNode nodeTo) {
    exists(Definition input, IRBlock block, int index, ExplicitDef def, SourceVariable v |
      nodeFrom.(InstructionNode).getSSAIntruction() = def.getInstruction() and
      input.definesAt(v, block, index) and
      def.getSourceVariable() = v and
      def.hasIndexInBlock(block, index) and
      nodeTo.hasInputAtRankInBlock(block, index, input)
    )
    or
    nodeTo.hasInputAtRankInBlock(_, _, nodeFrom.(SsaPhiNode).getPhiNode())
  }

  /**
   * Holds if `nodeFrom` is a read or write, and `nTo` is the next subsequent read of the variable
   * written (or read) by `storeOrRead`.
   */
  cached
  predicate ssaFlow(Node nodeFrom, Node nodeTo) {
    defUseFlow(nodeFrom, nodeTo)
    or
    fromPhiNode(nodeFrom, nodeTo)
    or
    toPhiNode(nodeFrom, nodeTo)
  }
}

import Cached

/**
 * Holds if the `i`'th write in block `bb` writes to the variable `v`.
 * `certain` is `true` if the write is guaranteed to overwrite the entire variable.
 */
predicate variableWrite(IRBlock bb, int i, SourceVariable v, boolean certain) {
  DataFlowImplCommon::forceCachingInSameStage() and
  exists(Def def |
    def.hasIndexInBlock(bb, i) and
    v = def.getSourceVariable() and
    (if def.isCertain() then certain = true else certain = false)
  )
}

/**
 * Holds if the `i`'th read in block `bb` reads to the variable `v`.
 * `certain` is `true` if the read is guaranteed. For C++, this is always the case.
 */
predicate variableRead(IRBlock bb, int i, SourceVariable v, boolean certain) {
  exists(Use use |
    v = use.getSourceVariable() and
    use.hasIndexInBlock(bb, i) and
    certain = true
  )
}
