import codeql.ssa.Ssa as SsaImpl
import semmle.code.cpp.ir.dataflow.internal.SsaImplCommon
import semmle.code.cpp.ir.dataflow.internal.SsaImpl as Existing
private import semmle.code.cpp.ir.implementation.raw.internal.TranslatedInitialization

signature module InputSig {
  class SourceVariable {
    predicate hasReadAtNode(Instruction instr);

    string toString();

    Location getLocation();
  }

  class DefInstruction extends Instruction {
    Instruction getAddress();

    SourceVariable getDefSourceVariable();
  }

  SourceVariable getReadSourceVariable(Instruction instr);
}

private predicate pointerStep(Instruction pred, Instruction succ) {
  succ.(ConvertInstruction).getUnary() = pred
  or
  succ.(CopyValueInstruction).getUnary() = pred
}

private Instruction getInitializationTargetAddress(IRVariable v) {
  exists(TranslatedVariableInitialization init |
    init.getIRVariable() = v and
    result = init.getTargetAddress()
  )
}

module Input0 implements InputSig {
  class SourceVariable extends IRVariable {
    predicate hasReadAtNode(Instruction instr) {
      exists(VariableAddressInstruction vai |
        vai.getIRVariable() = this and
        pointerStep*(vai, instr) and
        not pointerStep(instr, _)
      )
    }
  }

  class DefInstruction extends Instruction {
    IRVariable v;

    DefInstruction() {
      exists(Instruction initialize |
        initialize = getInitializationTargetAddress(v) and
        pointerStep*(initialize, this) and
        not pointerStep(this, _)
      )
    }

    SourceVariable getDefSourceVariable() { result = v }

    Instruction getAddress() { result = this }
  }

  private predicate flowsToStoreDestinationAddress(Instruction instr) {
    instr = any(StoreInstruction store).getDestinationAddress()
    or
    exists(Instruction succ |
      flowsToStoreDestinationAddress(succ) and
      pointerStep(instr, succ)
    )
  }

  SourceVariable getReadSourceVariable(Instruction instr) {
    result.hasReadAtNode(instr) and
    not flowsToStoreDestinationAddress(instr)
  }
}

module Input<InputSig Prev> implements InputSig {
  final private class FinalStoreInstruction = StoreInstruction;

  class DefInstruction extends FinalStoreInstruction {
    Instruction getAddress() { result = this.getResultAddress() }

    SourceVariable getDefSourceVariable() { result.hasReadAtNode(this.getDestinationAddress()) }
  }

  additional module SsaInput implements SsaImpl::InputSig<Location> {
    private predicate mayAlias(Prev::SourceVariable sv1, Prev::SourceVariable sv2) {
      sv1 = sv2
      or
      exists(StoreInstruction store |
        sv1.hasReadAtNode(store.getSourceValue()) and
        store.getDefSourceVariable() = sv2
      )
    }

    private module EquivalenceRelation =
      QlBuiltins::EquivalenceRelation<Prev::SourceVariable, mayAlias/2>;

    class SourceVariable extends EquivalenceRelation::EquivalenceClass {
      Prev::SourceVariable getAMember() { EquivalenceRelation::getEquivalenceClass(result) = this }

      string toString() { result = strictconcat(this.getAMember().toString(), ", ") }

      Location getLocation() {
        result =
          min(Prev::SourceVariable sv, Location loc |
            sv = this.getAMember() and loc = sv.getLocation()
          |
            sv order by loc.getStartLine(), loc.getStartColumn()
          ).getLocation()
      }
    }

    final private class FinalIRBlock = IRBlock;

    class BasicBlock extends FinalIRBlock {
      ControlFlowNode getNode(int i) { result = this.getInstruction(i) }

      int length() { result = this.getInstructionCount() }
    }

    class ControlFlowNode = Instruction;

    BasicBlock getImmediateBasicBlockDominator(BasicBlock bb) { result.immediatelyDominates(bb) }

    BasicBlock getABasicBlockSuccessor(BasicBlock bb) { result = bb.getASuccessor() }

    predicate variableWrite(BasicBlock bb, int i, SourceVariable v, boolean certain) {
      certain = true and
      exists(StoreInstruction store |
        bb.getInstruction(i) = store and
        v.getAMember().hasReadAtNode(store.getResultAddress())
      )
    }

    predicate variableRead(BasicBlock bb, int i, SourceVariable v, boolean certain) {
      certain = true and
      exists(LoadInstruction load, Instruction converted |
        pointerStep*(load, converted) and
        not pointerStep*(converted, _) and
        bb.getInstruction(i) = converted and
        v.getAMember() = Prev::getReadSourceVariable(load.getSourceAddress())
      )
    }
  }

  additional module Ssa = SsaImpl::Make<Location, SsaInput>;

  final private class Ssa0Definition = Ssa::Definition;

  class SourceVariable extends Ssa0Definition {
    predicate hasReadAtNode(Instruction instr) {
      exists(SsaInput::SourceVariable v, IRBlock bb, int i, LoadInstruction load |
        Ssa::ssaDefReachesRead(v, this, bb, i) and
        SsaInput::variableRead(bb, i, v, true) and
        bb.getInstruction(i) = load and
        pointerStep*(load, instr) and
        not pointerStep(instr, _)
      )
    }
  }

  private predicate flowsToStoreDestinationAddress(Instruction instr) {
    instr = any(StoreInstruction store).getDestinationAddress()
    or
    exists(Instruction succ |
      flowsToStoreDestinationAddress(succ) and
      pointerStep(instr, succ)
    )
  }

  SourceVariable getReadSourceVariable(Instruction instr) {
    result.hasReadAtNode(instr) and
    not flowsToStoreDestinationAddress(instr)
  }
}

module FinalInput = Input<Input0>;

module SsaInput = Input<FinalInput>::SsaInput;

module Ssa = Input<FinalInput>::Ssa;

Instruction getARead(Ssa::Definition def) {
  exists(SsaInput::SourceVariable v, IRBlock bb, int i |
    Ssa::ssaDefReachesRead(v, def, bb, i) and
    SsaInput::variableRead(bb, i, v, true) and
    bb.getInstruction(i) = result
  )
}

from Ssa::Definition d
select d
