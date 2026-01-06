/**
 * Provides Java-specific definitions for use in the `SsaReadPosition`.
 */
overlay[local?]
module;

private import cpp as C
private import semmle.code.cpp.dataflow.new.DataFlow::DataFlow::Ssa as Ssa
private import semmle.code.cpp.ir.IR as IR
private import SsaReadPositionCommon

class SsaVariable extends Ssa::Definition {
  SsaVariable() { this.isCertain() }
}

class SsaPhiNode = Ssa::PhiNode;

class BasicBlock = IR::IRCfg::BasicBlock;

/** Gets a basic block in which SSA variable `v` is read. */
BasicBlock getAReadBasicBlock(SsaVariable v) { result = v.getAUse().getDef().getBlock() }

private predicate id(C::Element x, C::Element y) { x = y }

private predicate idOfAst(C::Element x, int y) = equivalenceRelation(id/2)(x, y)

private predicate idOf(BasicBlock x, int y) { idOfAst(x.getFirstInstruction().getAst(), y) }

private int getId(BasicBlock bb) { idOf(bb, result) }

/**
 * Declarations to be exposed to users of SsaReadPositionCommon
 */
module Public {
  /**
   * Holds if `inp` is an input to `phi` along `edge` and this input has index `r`
   * in an arbitrary 1-based numbering of the input edges to `phi`.
   */
  predicate rankedPhiInput(SsaPhiNode phi, SsaVariable inp, SsaReadPositionPhiInputEdge edge, int r) {
    edge.phiInput(phi, inp) and
    edge =
      rank[r](SsaReadPositionPhiInputEdge e |
        e.phiInput(phi, _)
      |
        e order by getId(e.getOrigBlock())
      )
  }
}
