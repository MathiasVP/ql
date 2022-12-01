/**
 * This module defines an initial SSA pruning stage that doesn't take
 * indirections into account.
 */

private import codeql.ssa.Ssa as SsaImplCommon
private import semmle.code.cpp.ir.IR
private import semmle.code.cpp.ir.dataflow.internal.DataFlowImplCommon as DataFlowImplCommon
private import semmle.code.cpp.models.interfaces.Allocation as Alloc
private import semmle.code.cpp.models.interfaces.DataFlow as DataFlow
private import semmle.code.cpp.ir.implementation.raw.internal.SideEffects as SideEffects
private import semmle.code.cpp.ir.internal.IRCppLanguage
private import semmle.code.cpp.ir.dataflow.internal.DataFlowPrivate
private import semmle.code.cpp.ir.dataflow.internal.DataFlowUtil
private import semmle.code.cpp.ir.dataflow.internal.SsaInternalsCommon

private module Models {
  import semmle.code.cpp.models.interfaces.Iterator as Interfaces
  import semmle.code.cpp.models.implementations.Iterator as Iterator
  import semmle.code.cpp.models.implementations.StdContainer as StdContainer
}

private module SourceVariables {
  class SourceVariable instanceof BaseSourceVariable {
    string toString() { result = BaseSourceVariable.super.toString() }

    BaseSourceVariable getBaseVariable() { result = this }
  }

  class SourceIRVariable = BaseIRVariable;

  class CallVariable = BaseCallVariable;
}

import SourceVariables

private newtype TDefOrUseImpl =
  TDefImpl(Operand address) { isDef(_, _, address, _, _, _) } or
  TUseImpl(Operand operand) {
    isUse(_, operand, _, _, _) and
    not isDef(_, _, operand, _, _, _)
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

  abstract BaseSourceVariableInstruction getBase();

  final BaseSourceVariable getBaseSourceVariable() {
    result = this.getBase().getBaseSourceVariable()
  }

  /** Gets the variable that is defined or used. */
  final SourceVariable getSourceVariable() {
    exists(BaseSourceVariable v |
      result.getBaseVariable() = v and
      this.getBaseSourceVariable() = v
    )
  }
}

class DefImpl extends DefOrUseImpl, TDefImpl {
  Operand address;

  DefImpl() { this = TDefImpl(address) }

  override BaseSourceVariableInstruction getBase() { isDef(_, _, address, result, _, _) }

  Operand getAddressOperand() { result = address }

  Node0Impl getValue() { isDef(_, result, address, _, _, _) }

  override string toString() { result = address.toString() }

  override IRBlock getBlock() { result = this.getAddressOperand().getDef().getBlock() }

  override Cpp::Location getLocation() { result = this.getAddressOperand().getLocation() }

  final override predicate hasIndexInBlock(IRBlock block, int index) {
    this.getAddressOperand().getUse() = block.getInstruction(index)
  }

  predicate isCertain() { isDef(true, _, address, _, _, _) }

  final predicate cannotBePruned() {
    exists(Type t | t = this.getBase().getBaseSourceVariable().getType().getUnspecifiedType() |
      t instanceof Models::Iterator::Iterator and
      not t instanceof PointerOrReferenceType
    )
  }
}

class UseImpl extends DefOrUseImpl, TUseImpl {
  Operand operand;

  UseImpl() { this = TUseImpl(operand) }

  Operand getOperand() { result = operand }

  override string toString() { result = operand.toString() }

  final override predicate hasIndexInBlock(IRBlock block, int index) {
    operand.getUse() = block.getInstruction(index)
  }

  final override IRBlock getBlock() { result = operand.getUse().getBlock() }

  final override Cpp::Location getLocation() { result = operand.getLocation() }

  override BaseSourceVariableInstruction getBase() { isUse(_, operand, result, _, _) }

  predicate isCertain() { isUse(true, operand, _, _, _) }
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
    exists(DefImpl def | def.hasIndexInBlock(bb, i, v) |
      if def.isCertain() then certain = true else certain = false
    )
  }

  /**
   * Holds if the `i`'th read in block `bb` reads to the variable `v`.
   * `certain` is `true` if the read is guaranteed.
   */
  predicate variableRead(IRBlock bb, int i, SourceVariable v, boolean certain) {
    exists(UseImpl use | use.hasIndexInBlock(bb, i, v) |
      if use.isCertain() then certain = true else certain = false
    )
  }
}

private newtype TSsaDefOrUse =
  TDefOrUse(DefOrUseImpl defOrUse) {
    defOrUse instanceof UseImpl
    or
    // If `defOrUse` is a definition we only include it if the
    // SSA library concludes that it's live after the write.
    defOrUse.(DefImpl).cannotBePruned()
    or
    exists(Definition def, SourceVariable sv, IRBlock bb, int i |
      def.definesAt(sv, bb, i) and
      defOrUse.(DefImpl).hasIndexInBlock(bb, i, sv)
    )
  } or
  TPhi(PhiNode phi)

abstract private class SsaDefOrUse extends TSsaDefOrUse {
  string toString() { result = "SsaDefOrUse" }

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
}

class Phi extends TPhi, SsaDefOrUse {
  PhiNode phi;

  Phi() { this = TPhi(phi) }

  final override PhiNode asPhi() { result = phi }

  final override Location getLocation() { result = phi.getBasicBlock().getLocation() }

  Definition getAnInput() { Cached::lastRefRedef(result, _, _, phi) }
}

private Node0Impl getAnUltimateValueForDef(Definition def) {
  exists(IRBlock bb, int i, SourceVariable sv | def.definesAt(sv, bb, i) |
    result = getAnUltimateValueForDef(any(Phi phi | phi.asPhi() = def).getAnInput())
    or
    exists(DefOrUse defOrUse |
      defOrUse.asDefOrUse().hasIndexInBlock(bb, i, sv) and
      result = defOrUse.asDefOrUse().(DefImpl).getValue()
    )
  )
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

  override string toString() {
    result = this.asDefOrUse().toString()
    or
    this instanceof Phi and
    result = "Phi"
  }

  cached
  Node0Impl getAnUltimateValue() {
    // Use case
    exists(Definition def, IRBlock bb1, int i1, IRBlock bb2, int i2 |
      Cached::adjacentDefRead(def, bb1, i1, bb2, i2) and
      this.asDefOrUse().hasIndexInBlock(bb2, i2, def.getSourceVariable())
    |
      result = getAnUltimateValueForDef(def)
    )
    or
    // Phi case
    result = getAnUltimateValueForDef(this.asPhi())
  }
}

class Use extends DefOrUse {
  override UseImpl defOrUse;

  Operand getOperand() { result = defOrUse.getOperand() }

  Node0Impl getAnUltimateValue() {
    exists(Definition def, IRBlock bb1, int i1, IRBlock bb2, int i2 |
      Cached::adjacentDefRead(def, bb1, i1, bb2, i2) and
      defOrUse.hasIndexInBlock(bb2, i2, def.getSourceVariable())
    |
      result = getAnUltimateValueForDef(def)
    )
  }
}

class Def extends DefOrUse {
  override DefImpl defOrUse;

  Operand getAddressOperand() { result = defOrUse.getAddressOperand() }

  Instruction getAddress() { result = this.getAddressOperand().getDef() }

  Node0Impl getValue() { result = defOrUse.getValue() }

  override string toString() { result = this.asDefOrUse().toString() }

  predicate cannotBePruned() { defOrUse.cannotBePruned() }

  BaseSourceVariableInstruction getBase() { result = defOrUse.getBase() }
}

private module SsaImpl = SsaImplCommon::Make<SsaInput>;

class PhiNode = SsaImpl::PhiNode;

class Definition = SsaImpl::Definition;

cached
private module Cached {
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
}

private import Cached
