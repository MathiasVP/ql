private import cpp
private import semmle.code.cpp.ir.IR
private import semmle.code.cpp.ir.ValueNumbering
private import semmle.code.cpp.controlflow.IRGuards
private import codeql.util.Boolean
private import DataFlowUtil
private import DataFlowPrivate
private import SsaInternals as Ssa

private newtype TValueProperty =
  TEqConst(int k) { unaryComparesEq(_, _, k, _, any(BooleanValue bv)) } or
  TLtConst(int k) { unaryComparesLt(_, _, k, _, any(BooleanValue bv)) } or
  TEqValProp(Ssa::DefinitionExt other, int k) {
    // Rule out imprecise pointer reads
    other.getSourceVariable().getIndirection() = 1 and
    comparesEq(_, _, other.getARead().asOperand(), k, _, any(BooleanValue bv))
  } or
  TLtValProp(Ssa::DefinitionExt other, int k) {
    // Rule out imprecise pointer reads
    other.getSourceVariable().getIndirection() = 1 and
    comparesLt(_, _, other.getARead().asOperand(), k, _, any(BooleanValue bv))
  }

private class ValueProperty extends TValueProperty {
  string toString() {
    exists(int k |
      result = "== " + k and this = TEqConst(k)
      or
      result = "< " + k and this = TLtConst(k)
    )
    or
    exists(Ssa::DefinitionExt other, int k |
      this = TEqValProp(other, k) and
      result = "== " + other.toString() + " + " + k
      or
      this = TLtValProp(other, k) and
      result = "< " + other.toString() + " + " + k
    )
  }
}

private predicate isValPropGuard(
  Ssa::DefinitionExt flag, IRGuardCondition g, ValueProperty p, Boolean iseq, BooleanValue value
) {
  exists(int k |
    g.comparesEq(flag.getARead().asOperand(), k, iseq, value) and
    p = TEqConst(k)
    or
    g.comparesLt(flag.getARead().asOperand(), k, iseq, value) and
    p = TLtConst(k)
  )
  or
  exists(Ssa::DefinitionExt other, int k, boolean polarity |
    // In order for this property to be meaningful throughout the scope of the
    // flag, we need to ensure that the other variable is equally meaningful
    // and constant throughout the same scope.
    g.comparesEq(flag.getARead().asOperand(), other.getARead().asOperand(), k, iseq, polarity) and
    p = TEqValProp(other, k)
    or
    g.comparesLt(flag.getARead().asOperand(), other.getARead().asOperand(), k, iseq, polarity) and
    p = TLtValProp(other, k)
  |
    other.getBasicBlock().dominates(flag.getBasicBlock()) and
    value.getValue() = polarity.booleanXor(iseq).booleanNot()
  )
}

private predicate valPropGuardControls(
  Ssa::DefinitionExt flag, IRGuardCondition g, IRBlock bb, ValueProperty p, boolean iseq
) {
  exists(AbstractValue value |
    isValPropGuard(flag, g, p, iseq, value) and g.valueControls(bb, value)
  )
}

pragma[nomagic]
private predicate flagCandidate(Ssa::DefinitionExt flag, ValueProperty p) {
  2 <= strictcount(IRGuardCondition g | valPropGuardControls(flag, g, _, p, _)) and
  // TODO: Clean this up. We can use phi inputs nodes to remove this restriction.
  not flag.getSourceVariable()
      .getBaseVariable()
      .(Ssa::BaseIRVariable)
      .getIRVariable()
      .getAst()
      .getEnclosingElement*() = any(Loop loop).getStmt()
}

private predicate controlReachRev(Ssa::DefinitionExt flag, ValueProperty p, IRBlock bb) {
  exists(IRBlock controlled |
    flagCandidate(flag, p) and
    valPropGuardControls(flag, _, controlled, p, _) and
    bb.getASuccessor() = controlled and
    not valPropGuardControls(flag, _, bb, p, _)
  )
  or
  exists(IRBlock succ |
    bb.getASuccessor() = succ and
    controlReachRev(flag, p, succ) and
    not succ = flag.getBasicBlock()
  )
}

bindingset[bb]
pragma[inline_late]
private IRBlock getASuccessor(IRBlock bb) { result = bb.getASuccessor() }

bindingset[flag, p, bb]
pragma[inline_late]
private predicate controlReachRevLate(Ssa::DefinitionExt flag, ValueProperty p, IRBlock bb) {
  controlReachRev(flag, p, bb)
}

private predicate flagRelevant(Ssa::DefinitionExt flag, ValueProperty p, IRBlock bb) {
  exists(IRBlock prev |
    valPropGuardControls(flag, _, prev, p, _) and
    getASuccessor(prev) = bb and
    not valPropGuardControls(flag, _, bb, p, _) and
    controlReachRevLate(flag, p, bb)
  )
  or
  exists(IRBlock pred |
    flagRelevant(flag, p, pred) and
    getASuccessor(pred) = bb and
    controlReachRevLate(flag, p, bb)
  )
}

private newtype TSplitKind =
  TValuePropSplitKind(Ssa::DefinitionExt flag, ValueProperty p) { flagRelevant(flag, p, _) }

private newtype TSplit =
  TValuePropSplit(Ssa::DefinitionExt flag, ValueProperty p, Boolean iseq) {
    flagRelevant(flag, p, _)
  }

abstract class SplitKind extends TSplitKind {
  abstract string toString();

  abstract Location getLocation();

  abstract predicate inScope(NodeRegion n);
}

class ValuePropSplitKind extends SplitKind {
  private Ssa::DefinitionExt flag;
  private ValueProperty p;

  ValuePropSplitKind() { this = TValuePropSplitKind(flag, p) }

  override string toString() { result = flag.toString() + " " + p.toString() }

  override Location getLocation() { result = flag.getLocation() }

  override predicate inScope(NodeRegion nr) { flagRelevant(flag, p, nr) }
}

abstract class Split extends TSplit {
  abstract string toString();

  abstract Location getLocation();

  abstract SplitKind getKind();

  abstract predicate holds(NodeRegion n);
}

class ValuePropSplit extends Split {
  private Ssa::DefinitionExt flag;
  private ValueProperty p;
  private boolean iseq;

  ValuePropSplit() { this = TValuePropSplit(flag, p, iseq) }

  override string toString() { result = this.getKind().toString() + " is " + iseq }

  override Location getLocation() { result = flag.getLocation() }

  override SplitKind getKind() { result = TValuePropSplitKind(flag, p) }

  override predicate holds(NodeRegion nr) { valPropGuardControls(flag, _, nr, p, iseq) }
}
