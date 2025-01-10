private import cpp as Cpp
private import SsaInternals as Ssa
private import codeql.ssa.Ssa as SsaImplCommon
private import DataFlowPrivate
private import semmle.code.cpp.ir.IR
private import DataFlowUtil

private module SsaInput implements SsaImplCommon::InputSig<Cpp::Location> {
  import SsaInternalsCommon::InputSigCommon

  class SourceVariable = Ssa::SourceVariable;

  /**
   * Holds if `instr` flows to the destination address of a `StoreInstruction`
   */
  private predicate rev(Node n) {
    n.asInstruction() = any(StoreInstruction store).getDestinationAddress()
    or
    exists(Node n1 |
      rev(n1) and
      simpleLocalFlowStepWithoutAliasing(n, n1, _)
    )
  }

  /**
   * Holds if `instr` flows to the destination address of a `StoreInstruction`
   * and flows from a read of some definition.
   */
  private predicate fwd(Node n) {
    rev(n) and
    (
      any(Ssa::Def def |
        not def.getSourceVariable().getBaseVariable() instanceof Ssa::BaseCallVariable
      ).getARead() = n
      or
      exists(Node n0 |
        fwd(n0) and
        simpleLocalFlowStepWithoutAliasing(n0, n, _)
      )
    )
  }

  /**
   * This predicate holds if
   * ```
   * conversionFlow(instr1.getAUse(), instr2, _, false)
   * ```
   * and both `instr1` and `instr2` are instructions on a path from a read of
   * some definition to the destination address of a `StoreInstruction`.
   */
  private predicate flow(Node n1, Node n2) {
    fwd(n1) and
    fwd(n2) and
    simpleLocalFlowStepWithoutAliasing(n1, n2, _)
  }

  /** Holds if a a read of `def` flows to the destination address of `store`. */
  private predicate defFlowsToDestinationOfStore(Ssa::Def addr, Ssa::Def def) {
    flow*(addr.getARead(), instructionNode(def.getAddress()))
  }

  /**
   * Holds if `def` is "ultimately" (recursively, through phi definitions) defined
   * by `store` which writes to `value`.
   */
  private predicate hasAnUltimateDefinition(
    Ssa::Def def, Ssa::SourceVariable value, StoreInstruction store
  ) {
    exists(IRBlock bb, int i |
      def.getAnUltimateDefinition().hasIndexInBlock(bb, i, value) and
      bb.getInstruction(i) = store
    )
  }

  /**
   * Holds if the `i`'th instruction in `bb` writes to `v` through an alias.
   * `certain` is `true` if write is guaranteed to overwrite the entire
   * allocation.
   */
  predicate variableWrite(BasicBlock bb, int i, SourceVariable v, boolean certain) {
    exists(
      Ssa::Def addrDef, Ssa::SourceVariable value, StoreInstruction store0, Ssa::UseImpl addr,
      int k, Ssa::Def def
    |
      // def is the i'th instruction in `bb`
      def.hasIndexInBlock(bb, i, _) and
      // def writes to `addrDef`.
      defFlowsToDestinationOfStore(addrDef, def) and
      // addrDef can be defined by `store0`
      hasAnUltimateDefinition(addrDef, value, store0) and
      // `addr` is the value that is written to `value` by `store0`
      addr.getNode().asOperand() = store0.getSourceValueOperand() and
      not addr.getBaseSourceVariable() instanceof Ssa::BaseCallVariable and
      addr.getIndirection() + k = value.getIndirection() and
      v = addr.getSourceVariable().getIndirectVariable(k) and
      if def.isCertain() then certain = true else certain = false
    )
  }

  additional predicate variableRead(
    BasicBlock bb, int i, SourceVariable v, boolean certain, Ssa::UseImpl use
  ) {
    certain = true and
    use.hasIndexInBlock(bb, i, v)
  }

  predicate variableRead(BasicBlock bb, int i, SourceVariable v, boolean certain) {
    variableRead(bb, i, v, certain, _)
  }
}

private module AliasedSsa = SsaImplCommon::Make<Cpp::Location, SsaInput>;

predicate aliasedFlow(Node node1, Node node2) {
  exists(IRBlock bb1, int i1, AliasedSsa::DefinitionExt def, SsaInput::SourceVariable sv |
    def.definesAt(sv, bb1, i1, _)
  |
    bb1.getInstruction(i1) = node1.asInstruction() and
    exists(IRBlock bb2, int i2, Ssa::UseImpl use |
      AliasedSsa::adjacentDefReadExt(def, sv, bb1, i1, bb2, i2) and
      SsaInput::variableRead(bb2, i2, sv, _, use) and
      use.getNode() = node2
    )
    // TODO: We also want to allow `node2` to be a phi node (as constructed by
    // `AliasedSsa`), but creating adding a `TNode` branch based on `AliasedSsa`
    // leads to non-monotonic recursion. We should refactor the dataflow library
    // so that this dosn't happen, but for now we simply don't generate these
    // phi nodes.
  )
}
