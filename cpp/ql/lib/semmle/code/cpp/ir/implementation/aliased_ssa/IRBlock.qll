/**
 * Provides classes describing basic blocks in the IR of a function.
 */

private import internal.IRInternal
import Instruction
private import internal.IRBlockImports as Imports
import Imports::EdgeKind
private import Cached

/**
 * Holds if `block` is a block in `func` and `sortOverride`, `sortKey1`, and `sortKey2` are the
 * sort keys of the block (derived from its first instruction)
 */
pragma[nomagic]
private predicate blockSortKeys(
  IRFunction func, IRBlockBase block, int sortOverride, int sortKey1, int sortKey2
) {
  block.getEnclosingIRFunction() = func and
  block.getFirstInstruction().hasSortKeys(sortKey1, sortKey2) and
  // Ensure that the block containing `EnterFunction` always comes first.
  if block.getFirstInstruction() instanceof EnterFunctionInstruction
  then sortOverride = 0
  else sortOverride = 1
}

/**
 * A basic block in the IR. A basic block consists of a sequence of `Instructions` with the only
 * incoming edges at the beginning of the sequence and the only outgoing edges at the end of the
 * sequence.
 *
 * This class does not contain any members that query the predecessor or successor edges of the
 * block. This allows different classes that extend `IRBlockBase` to expose different subsets of
 * edges (e.g. ignoring unreachable edges).
 *
 * Most consumers should use the class `IRBlock`.
 */
class IRBlockBase extends TIRBlock {
  /** Gets a textual representation of this block. */
  final string toString() {
    exists(Construction::TStageInstruction firstInstr, Opcode opcode, Language::AST ast |
      this = MkIRBlock(firstInstr) and
      Construction::getInstructionOpcode(opcode, firstInstr) and
      ast = Construction::getInstructionAst(firstInstr) and
      result = opcode.toString() + ": " + ast.toString()
    )
  }

  /** Gets the source location of the first non-`Phi` instruction in this block. */
  final Language::Location getLocation() { result = this.getFirstInstruction().getLocation() }

  /**
   * INTERNAL: Do not use.
   *
   * Gets the zero-based index of the block within its function.
   *
   * This predicate is used by debugging and printing code only.
   */
  int getDisplayIndex() {
    exists(IRConfiguration::IRConfiguration config |
      config.shouldEvaluateDebugStringsForFunction(this.getEnclosingFunction())
    ) and
    exists(IRFunction func |
      this =
        rank[result + 1](IRBlock funcBlock, int sortOverride, int sortKey1, int sortKey2 |
          blockSortKeys(func, funcBlock, sortOverride, sortKey1, sortKey2)
        |
          funcBlock order by sortOverride, sortKey1, sortKey2
        )
    )
  }

  /**
   * Gets the `index`th non-`Phi` instruction in this block.
   */
  final Instruction getInstruction(int index) { result = this.getInstruction0(index) }

  /**
   * Gets the `index`th non-`Phi` instruction in this block.
   */
  final Construction::TStageInstruction getInstruction0(int index) {
    result = getInstruction(this, index)
  }

  /**
   * Get the `Phi` instructions that appear at the start of this block.
   */
  final PhiInstruction getAPhiInstruction() { result = this.getAPhiInstruction0() }

  final Construction::TStageInstruction getAPhiInstruction0() {
    Construction::getPhiInstructionBlockStart(result) = getFirstInstruction(this)
  }

  /**
   * Gets an instruction in this block. This includes `Phi` instructions.
   */
  final Instruction getAnInstruction() {
    result = this.getInstruction(_) or
    result = this.getAPhiInstruction()
  }

  final Construction::TStageInstruction getAnInstruction0() {
    result = this.getInstruction0(_) or
    result = this.getAPhiInstruction0()
  }

  /**
   * Gets the first non-`Phi` instruction in this block.
   */
  final Instruction getFirstInstruction() { result = this.getFirstInstruction0() }

  final Construction::TStageInstruction getFirstInstruction0() {
    result = getFirstInstruction(this)
  }

  /**
   * Gets the last instruction in this block.
   */
  final Instruction getLastInstruction() {
    result = this.getInstruction(this.getInstructionCount() - 1)
  }

  /**
   * Gets the number of non-`Phi` instructions in this block.
   */
  final int getInstructionCount() { result = getInstructionCount(this) }

  /**
   * Gets the `IRFunction` that contains this block.
   */
  final IRFunction getEnclosingIRFunction() {
    exists(Construction::TStageInstruction firstInstr |
      this = MkIRBlock(firstInstr) and
      result = Construction::getInstructionEnclosingIRFunction(firstInstr)
    )
  }

  /**
   * Gets the `Function` that contains this block.
   */
  final Language::Declaration getEnclosingFunction() {
    result = this.getEnclosingIRFunction().getFunction()
  }
}

private TIRBlock getABlockSuccessor(TIRBlock b) { blockSuccessor(b, result) }

private TIRBlock getABlockPredecessor(TIRBlock b) { b = getABlockSuccessor(result) }

pragma[nomagic]
private IRBlockBase getEntryBlock(IRFunction f) {
  result.getFirstInstruction0() = f.getEnterFunctionInstruction()
}

private predicate isReachableFromFunctionEntry(TIRBlock b) {
  exists(Construction::TStageInstruction firstInstr, IRFunction f |
    b = MkIRBlock(firstInstr) and
    f = Construction::getInstructionEnclosingIRFunction(firstInstr) and
    b = getEntryBlock(f)
  )
  or
  isReachableFromFunctionEntry(getABlockPredecessor(b))
}

/**
 * A basic block with additional information about its predecessor and successor edges. Each edge
 * corresponds to the control flow between the last instruction of one block and the first
 * instruction of another block.
 */
class IRBlock extends IRBlockBase {
  IRBlock() { isReachableFromFunctionEntry(this) }

  /**
   * Gets a block to which control flows directly from this block.
   */
  final IRBlock getASuccessor() { result = getABlockSuccessor(this) }

  /**
   * Gets a block from which control flows directly to this block.
   */
  final IRBlock getAPredecessor() { result = getABlockPredecessor(this) }

  /**
   * Gets the block to which control flows directly from this block along an edge of kind `kind`.
   */
  final IRBlock getSuccessor(EdgeKind kind) { blockSuccessor(this, result, kind) }

  /**
   * Gets the block to which control flows directly from this block along a back edge of kind
   * `kind`.
   */
  final IRBlock getBackEdgeSuccessor(EdgeKind kind) { backEdgeSuccessor(this, result, kind) }

  /**
   * Holds if this block immediately dominates `block`.
   *
   * Block `A` immediate dominates block `B` if block `A` strictly dominates block `B` and block `B`
   * is a direct successor of block `A`.
   */
  final predicate immediatelyDominates(IRBlock block) { blockImmediatelyDominates(this, block) }

  /**
   * Holds if this block strictly dominates `block`.
   *
   * Block `A` strictly dominates block `B` if block `A` dominates block `B` and blocks `A` and `B`
   * are not the same block.
   */
  final predicate strictlyDominates(IRBlock block) { blockImmediatelyDominates+(this, block) }

  /**
   * Holds if this block dominates `block`.
   *
   * Block `A` dominates block `B` if any control flow path from the entry block of the function to
   * block `B` must pass through block `A`. A block always dominates itself.
   */
  final predicate dominates(IRBlock block) { this.strictlyDominates(block) or this = block }

  /**
   * Gets a block on the dominance frontier of this block.
   *
   * The dominance frontier of block `A` is the set of blocks `B` such that block `A` does not
   * dominate block `B`, but block `A` does dominate an immediate predecessor of block `B`.
   */
  pragma[noinline]
  final IRBlock dominanceFrontier() {
    this.getASuccessor() = result and
    not this.immediatelyDominates(result)
    or
    exists(IRBlock prev | result = prev.dominanceFrontier() |
      this.immediatelyDominates(prev) and
      not this.immediatelyDominates(result)
    )
  }

  /**
   * Holds if this block immediately post-dominates `block`.
   *
   * Block `A` immediate post-dominates block `B` if block `A` strictly post-dominates block `B` and
   * block `B` is a direct successor of block `A`.
   */
  final predicate immediatelyPostDominates(IRBlock block) {
    blockImmediatelyPostDominates(this, block)
  }

  /**
   * Holds if this block strictly post-dominates `block`.
   *
   * Block `A` strictly post-dominates block `B` if block `A` post-dominates block `B` and blocks `A`
   * and `B` are not the same block.
   */
  final predicate strictlyPostDominates(IRBlock block) {
    blockImmediatelyPostDominates+(this, block)
  }

  /**
   * Holds if this block is a post-dominator of `block`.
   *
   * Block `A` post-dominates block `B` if any control flow path from `B` to the exit block of the
   * function must pass through block `A`. A block always post-dominates itself.
   */
  final predicate postDominates(IRBlock block) { this.strictlyPostDominates(block) or this = block }

  /**
   * Gets a block on the post-dominance frontier of this block.
   *
   * The post-dominance frontier of block `A` is the set of blocks `B` such that block `A` does not
   * post-dominate block `B`, but block `A` does post-dominate an immediate successor of block `B`.
   */
  pragma[noinline]
  final IRBlock postDominanceFrontier() {
    this.getAPredecessor() = result and
    not this.immediatelyPostDominates(result)
    or
    exists(IRBlock prev | result = prev.postDominanceFrontier() |
      this.immediatelyPostDominates(prev) and
      not this.immediatelyPostDominates(result)
    )
  }

  /**
   * Holds if this block is reachable from the entry block of its function.
   */
  final predicate isReachableFromFunctionEntry() { isReachableFromFunctionEntry(this) }
}

private predicate startsBasicBlock(Construction::TStageInstruction instr) {
  not instr instanceof Construction::SsaInstructions::TPhiInstruction and
  not adjacentInBlock(_, instr)
}

/** Holds if `i2` follows `i1` in a `IRBlock`. */
private predicate adjacentInBlock(
  Construction::TStageInstruction i1, Construction::TStageInstruction i2
) {
  // - i2 must be the only successor of i1
  i2 = unique( | | Construction::getInstructionSuccessor(i1, _)) and
  // - i1 must be the only predecessor of i2
  i1 = unique(Construction::TStageInstruction i | Construction::getInstructionSuccessor(i, _) = i2) and
  // - The edge between the two must be a GotoEdge. We just check that one
  //   exists since we've already checked that it's unique.
  exists(GotoEdge edgeKind | exists(Construction::getInstructionSuccessor(i1, edgeKind))) and
  // - The edge must not be a back edge. This means we get the same back edges
  //   in the basic-block graph as we do in the raw CFG.
  not exists(Construction::getInstructionBackEdgeSuccessor(i1, _))
  // This predicate could be simplified to remove one of the `unique`s if we
  // were willing to rely on the CFG being well-formed and thus never having
  // more than one successor to an instruction that has a `GotoEdge` out of it.
}

private predicate isEntryBlock(TIRBlock block) {
  block = MkIRBlock(any(EnterFunctionInstruction enter))
}

cached
private module Cached {
  cached
  newtype TIRBlock =
    MkIRBlock(Construction::TStageInstruction firstInstr) { startsBasicBlock(firstInstr) }

  /** Holds if `i` is the `index`th instruction the block starting with `first`. */
  private Construction::TStageInstruction getInstructionFromFirst(
    Construction::TStageInstruction first, int index
  ) = shortestDistances(startsBasicBlock/1, adjacentInBlock/2)(first, result, index)

  /** Holds if `i` is the `index`th instruction in `block`. */
  cached
  Construction::TStageInstruction getInstruction(TIRBlock block, int index) {
    result = getInstructionFromFirst(getFirstInstruction(block), index)
  }

  cached
  int getInstructionCount(TIRBlock block) { result = strictcount(getInstruction(block, _)) }

  cached
  predicate blockSuccessor(TIRBlock pred, TIRBlock succ, EdgeKind kind) {
    exists(Construction::TStageInstruction predLast, Construction::TStageInstruction succFirst |
      predLast = getInstruction(pred, getInstructionCount(pred) - 1) and
      succFirst = Construction::getInstructionSuccessor(predLast, kind) and
      succ = MkIRBlock(succFirst)
    )
  }

  pragma[noinline]
  private predicate blockIdentity(TIRBlock b1, TIRBlock b2) { b1 = b2 }

  pragma[noopt]
  cached
  predicate backEdgeSuccessor(TIRBlock pred, TIRBlock succ, EdgeKind kind) {
    backEdgeSuccessorRaw(pred, succ, kind)
    or
    // See the QLDoc on `backEdgeSuccessorRaw`.
    exists(TIRBlock pred2 |
      // Joining with `blockIdentity` is a performance trick to get
      // `forwardEdgeRaw` on the RHS of a join, where it's fast.
      blockIdentity(pred, pred2) and
      forwardEdgeRaw+(pred, pred2)
    ) and
    blockSuccessor(pred, succ, kind)
  }

  /**
   * Holds if there is an edge from `pred` to `succ` that is not a back edge.
   */
  private predicate forwardEdgeRaw(TIRBlock pred, TIRBlock succ) {
    exists(EdgeKind kind |
      blockSuccessor(pred, succ, kind) and
      not backEdgeSuccessorRaw(pred, succ, kind)
    )
  }

  /**
   * Holds if the `kind`-edge from `pred` to `succ` is a back edge according to
   * `Construction`.
   *
   * There could be loops of non-back-edges if there is a flaw in the IR
   * construction or back-edge detection, and this could cause non-termination
   * of subsequent analysis. To prevent that, a subsequent predicate further
   * classifies all edges as back edges if they are involved in a loop of
   * non-back-edges.
   */
  private predicate backEdgeSuccessorRaw(TIRBlock pred, TIRBlock succ, EdgeKind kind) {
    exists(Instruction predLast, Instruction succFirst |
      predLast = getInstruction(pred, getInstructionCount(pred) - 1) and
      succFirst = Construction::getInstructionBackEdgeSuccessor(predLast, kind) and
      succ = MkIRBlock(succFirst)
    )
  }

  cached
  predicate blockSuccessor(TIRBlock pred, TIRBlock succ) { blockSuccessor(pred, succ, _) }

  cached
  predicate blockImmediatelyDominates(TIRBlock dominator, TIRBlock block) =
    idominance(isEntryBlock/1, blockSuccessor/2)(_, dominator, block)
}

private Construction::TStageInstruction getFirstInstruction(TIRBlock block) {
  block = MkIRBlock(result)
}

private predicate blockFunctionExit(IRBlock exit) {
  exit.getLastInstruction() instanceof ExitFunctionInstruction
}

private predicate blockPredecessor(IRBlock src, IRBlock pred) { src.getAPredecessor() = pred }

private predicate blockImmediatelyPostDominates(IRBlock postDominator, IRBlock block) =
  idominance(blockFunctionExit/1, blockPredecessor/2)(_, postDominator, block)
