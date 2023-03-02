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
    not isDef(true, _, operand, _, _, _)
  } or
  TGlobalUse(Cpp::GlobalOrNamespaceVariable v, IRFunction f) {
    // Represents a final "use" of a global variable to ensure that
    // the assignment to a global variable isn't ruled out as dead.
    exists(VariableAddressInstruction vai |
      vai.getEnclosingIRFunction() = f and
      vai.getAstVariable() = v and
      isDef(_, _, _, vai, _, _)
    )
  } or
  TGlobalDefImpl(Cpp::GlobalOrNamespaceVariable v, IRFunction f) {
    // Represents the initial "definition" of a global variable when entering
    // a function body.
    exists(VariableAddressInstruction vai |
      vai.getEnclosingIRFunction() = f and
      vai.getAstVariable() = v and
      isUse(_, _, vai, _, _) and
      not isDef(_, _, vai.getAUse(), _, _, _)
    )
  } or
  TIteratorDef(BaseSourceVariableInstruction container, Operand iteratorAddress) {
    isIteratorDef(container, iteratorAddress, _, _, _)
  } or
  TIteratorUse(BaseSourceVariableInstruction container, Operand iteratorAddress) {
    isIteratorUse(container, iteratorAddress, _, _)
  } or
  TFinalParameterUse(Parameter p) {
    any(Indirection indirection).getType() = p.getUnspecifiedType()
  }

abstract private class DefOrUseImpl extends TDefOrUseImpl {
  /** Gets a textual representation of this element. */
  abstract string toString();

  /** Gets the block of this definition or use. */
  final IRBlock getBlock() { this.hasIndexInBlock(result, _) }

  /** Holds if this definition or use has index `index` in block `block`. */
  abstract predicate hasIndexInBlock(IRBlock block, int index);

  final predicate hasIndexInBlock(IRBlock block, int index, SourceVariable sv) {
    this.hasIndexInBlock(block, index) and
    sv = this.getSourceVariable()
  }

  /** Gets the location of this element. */
  abstract Cpp::Location getLocation();

  abstract BaseSourceVariableInstruction getBase();

  BaseSourceVariable getBaseSourceVariable() { result = this.getBase().getBaseSourceVariable() }

  /** Gets the variable that is defined or used. */
  final SourceVariable getSourceVariable() {
    result.getBaseVariable() = this.getBaseSourceVariable()
  }

  abstract predicate isCertain();
}

abstract class DefImpl extends DefOrUseImpl {
  Operand address;

  Operand getAddressOperand() { result = address }

  abstract Node0Impl getValue();

  override string toString() { result = address.toString() }

  override Cpp::Location getLocation() { result = this.getAddressOperand().getLocation() }

  final override predicate hasIndexInBlock(IRBlock block, int index) {
    this.getAddressOperand().getUse() = block.getInstruction(index)
  }
}

private class DirectDef extends DefImpl, TDefImpl {
  DirectDef() { this = TDefImpl(address) }

  override BaseSourceVariableInstruction getBase() { isDef(_, _, address, result, _, _) }

  override Node0Impl getValue() { isDef(_, result, address, _, _, _) }

  override predicate isCertain() { isDef(true, _, address, _, _, _) }
}

private class IteratorDef extends DefImpl, TIteratorDef {
  BaseSourceVariableInstruction container;

  IteratorDef() { this = TIteratorDef(container, address) }

  override BaseSourceVariableInstruction getBase() { result = container }

  override Node0Impl getValue() { isIteratorDef(_, address, result, _, _) }

  override predicate isCertain() { none() }
}

abstract class UseImpl extends DefOrUseImpl { }

abstract private class OperandBasedUse extends UseImpl {
  Operand operand;

  override string toString() { result = operand.toString() }

  final override predicate hasIndexInBlock(IRBlock block, int index) {
    operand.getUse() = block.getInstruction(index)
  }

  final override Cpp::Location getLocation() { result = operand.getLocation() }

  final Operand getOperand() { result = operand }
}

private class DirectUse extends OperandBasedUse, TUseImpl {
  DirectUse() { this = TUseImpl(operand) }

  override BaseSourceVariableInstruction getBase() { isUse(_, operand, result, _, _) }

  override predicate isCertain() { isUse(true, operand, _, _, _) }
}

private class IteratorUse extends OperandBasedUse, TIteratorUse {
  BaseSourceVariableInstruction container;

  IteratorUse() { this = TIteratorUse(container, operand) }

  override BaseSourceVariableInstruction getBase() { result = container }

  override predicate isCertain() { none() }
}

private class FinalParameterUse extends UseImpl, TFinalParameterUse {
  Parameter p;

  FinalParameterUse() { this = TFinalParameterUse(p) }

  override string toString() { result = p.toString() }

  final override predicate hasIndexInBlock(IRBlock block, int index) {
    // Ideally, this should always be a `ReturnInstruction`, but if
    // someone forgets to write a `return` statement in a function
    // with a non-void return type we generate an `UnreachedInstruction`.
    // In this case we still want to generate flow out of such functions
    // if they write to a parameter. So we pick the index of the
    // `UnreachedInstruction` as the index of this use.
    // Note that a function may have both a `ReturnInstruction` and an
    // `UnreachedInstruction`. If that's the case this predicate will
    // return multiple results. I don't think this is detrimental to
    // performance, however.
    exists(Instruction return |
      return instanceof ReturnInstruction or
      return instanceof UnreachedInstruction
    |
      block.getInstruction(index) = return and
      return.getEnclosingFunction() = p.getFunction()
    )
  }

  final override Cpp::Location getLocation() {
    // Parameters can have multiple locations. When there's a unique location we use
    // that one, but if multiple locations exist we default to an unknown location.
    result = unique( | | p.getLocation())
    or
    not exists(unique( | | p.getLocation())) and
    result instanceof UnknownDefaultLocation
  }

  override BaseSourceVariableInstruction getBase() {
    exists(InitializeParameterInstruction init |
      init.getParameter() = p and
      // This is always a `VariableAddressInstruction`
      result = init.getAnOperand().getDef()
    )
  }

  override predicate isCertain() { any() }
}

class GlobalUse extends UseImpl, TGlobalUse {
  Cpp::GlobalOrNamespaceVariable global;
  IRFunction f;

  GlobalUse() { this = TGlobalUse(global, f) }

  /** Gets the global variable associated with this use. */
  Cpp::GlobalOrNamespaceVariable getVariable() { result = global }

  /** Gets the `IRFunction` whose body is exited from after this use. */
  IRFunction getIRFunction() { result = f }

  final override predicate hasIndexInBlock(IRBlock block, int index) {
    exists(ExitFunctionInstruction exit |
      exit = f.getExitFunctionInstruction() and
      block.getInstruction(index) = exit
    )
  }

  final override Cpp::Location getLocation() { result = f.getLocation() }

  override BaseSourceVariable getBaseSourceVariable() {
    result.(BaseIRVariable).getIRVariable().getAst() = global
  }

  /**
   * Gets the type of this use after specifiers have been deeply stripped
   * and typedefs have been resolved.
   */
  Type getUnspecifiedType() { result = global.getUnspecifiedType() }

  override predicate isCertain() { any() }

  override string toString() { result = "GlobalUse" }

  override BaseSourceVariableInstruction getBase() { none() }
}

class GlobalDefImpl extends DefOrUseImpl, TGlobalDefImpl {
  Cpp::GlobalOrNamespaceVariable global;
  IRFunction f;

  GlobalDefImpl() { this = TGlobalDefImpl(global, f) }

  /** Gets the global variable associated with this definition. */
  Cpp::GlobalOrNamespaceVariable getVariable() { result = global }

  /** Gets the `IRFunction` whose body is evaluated after this definition. */
  IRFunction getIRFunction() { result = f }

  /** Holds if this definition or use has index `index` in block `block`. */
  final override predicate hasIndexInBlock(IRBlock block, int index) {
    exists(EnterFunctionInstruction enter |
      enter = f.getEnterFunctionInstruction() and
      block.getInstruction(index) = enter
    )
  }

  override BaseSourceVariable getBaseSourceVariable() {
    result.(BaseIRVariable).getIRVariable().getAst() = global
  }

  /**
   * Gets the type of this use after specifiers have been deeply stripped
   * and typedefs have been resolved.
   */
  Type getUnspecifiedType() { result = global.getUnspecifiedType() }

  override string toString() { result = "GlobalDef" }

  override Location getLocation() { result = f.getLocation() }

  override BaseSourceVariableInstruction getBase() { none() }

  override predicate isCertain() { any() }
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
      exists(DefImpl def | def.hasIndexInBlock(bb, i, v) |
        if def.isCertain() then certain = true else certain = false
      )
      or
      exists(GlobalDefImpl global |
        global.hasIndexInBlock(bb, i, v) and
        certain = true
      )
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

cached
module SsaCached {
  /**
   * Holds if the SSA definition of `v` at `def` reaches a read at index `i` in
   * basic block `bb`, without crossing another SSA definition of `v`.
   */
  private predicate ssaDefReachesRead(SourceVariable sv, IRBlock bb, int i) {
    SsaImpl::ssaDefReachesRead(sv, _, bb, i)
  }

  cached
  newtype TSsaDefOrUse =
    TDefOrUse(DefOrUseImpl defOrUse) {
      exists(IRBlock bb, int i, SourceVariable sv |
        ssaDefReachesRead(sv, bb, i) and
        defOrUse.(UseImpl).hasIndexInBlock(bb, i, sv)
      )
      or
      // If `defOrUse` is a definition we only include it if the
      // SSA library concludes that it's live after the write.
      exists(Definition def, SourceVariable sv, IRBlock bb, int i |
        def.definesAt(sv, bb, i) and
        defOrUse.(DefImpl).hasIndexInBlock(bb, i, sv)
      )
    } or
    TPhi(PhiNode phi) or
    TGlobalDef(GlobalDefImpl global) {
      exists(Definition def, SourceVariable sv, IRBlock bb, int i |
        def.definesAt(sv, bb, i) and
        global.hasIndexInBlock(bb, i, sv)
      )
    }
}

private import SsaCached

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

class GlobalDef extends TGlobalDef, SsaDefOrUse {
  GlobalDefImpl global;

  GlobalDef() { this = TGlobalDef(global) }

  /** Gets the location of this definition. */
  final override Location getLocation() { result = global.getLocation() }

  /** Gets a textual representation of this definition. */
  override string toString() { result = "GlobalDef" }

  /**
   * Holds if this definition has index `index` in block `block`, and
   * is a definition of the variable `sv`.
   */
  predicate hasIndexInBlock(IRBlock block, int index, SourceVariable sv) {
    global.hasIndexInBlock(block, index, sv)
  }

  /**
   * Gets the type of this definition after specifiers have been deeply stripped
   * and typedefs have been resolved.
   */
  DataFlowType getUnspecifiedType() { result = global.getUnspecifiedType() }

  /** Gets the `IRFunction` whose body is evaluated after this definition. */
  IRFunction getIRFunction() { result = global.getIRFunction() }

  /** Gets the global variable associated with this definition. */
  Cpp::GlobalOrNamespaceVariable getVariable() { result = global.getVariable() }
}

pragma[nomagic]
predicate globalDefHasFunctionAndVariable(
  GlobalDef globalDef, IRFunction func, Cpp::GlobalOrNamespaceVariable v
) {
  globalDef.getIRFunction() = func and
  globalDef.getVariable() = v
}

pragma[nomagic]
predicate globalUseHasFunctionAndVariable(
  GlobalUse globalUse, IRFunction func, Cpp::GlobalOrNamespaceVariable v
) {
  globalUse.getIRFunction() = func and
  globalUse.getVariable() = v
}

class Phi extends TPhi, SsaDefOrUse {
  PhiNode phi;

  Phi() { this = TPhi(phi) }

  final override PhiNode asPhi() { result = phi }

  final override Location getLocation() { result = phi.getBasicBlock().getLocation() }
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
}

class Def extends DefOrUse {
  override DefImpl defOrUse;

  Operand getAddressOperand() { result = defOrUse.getAddressOperand() }

  Instruction getAddress() { result = this.getAddressOperand().getDef() }

  Node0Impl getValue() { result = defOrUse.getValue() }

  override string toString() { result = this.asDefOrUse().toString() }

  BaseSourceVariableInstruction getBase() { result = defOrUse.getBase() }

  predicate isIteratorDef() { defOrUse instanceof IteratorDef }
}

class Use extends DefOrUse {
  override UseImpl defOrUse;

  /**
   * Gets the operand associated with this use, if any.
   */
  Operand getAddressOperand() { result = defOrUse.(OperandBasedUse).getOperand() }

  predicate isGlobalUseInFunction(Cpp::GlobalOrNamespaceVariable v, IRFunction f) {
    globalUseHasFunctionAndVariable(defOrUse, f, v)
  }
}

private module SsaImpl = SsaImplCommon::Make<SsaInput>;

class PhiNode = SsaImpl::PhiNode;

class Definition = SsaImpl::Definition;
