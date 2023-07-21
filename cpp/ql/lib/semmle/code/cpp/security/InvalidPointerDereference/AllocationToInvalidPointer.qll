/**
 * This file provides the first phase of the `cpp/invalid-pointer-deref` query that identifies flow
 * from an allocation to a pointer-arithmetic instruction that constructs a pointer that is out of bounds.
 *
 * Consider the following snippet:
 * ```cpp
 * 1. char* base = (char*)malloc(size);
 * 2. char* end = base + size;
 * 3. for(int *p = base; p <= end; p++) {
 * 4.   use(*p);
 * 5. }
 * ```
 * this file identifies the flow from `new int[size]` to `base + size`.
 *
 * This is done using the product-flow library. The configuration tracks flow from the pair
 * `(allocation, size of allocation)` to a pair `(a, b)` where there exists a pointer-arithmetic instruction
 * `pai = a + r` such that `b` is a dataflow node where `b <= r`. Because there will be a dataflow-path from
 * `allocation` to `a` this means that the `pai` will compute a pointer that's some number of elements away
 * from the end position in the allocation. See `pointerAddInstructionHasBounds` for the implementation of this.
 *
 * In the above example, the pair `(a, b)` is `(base, size)` from the expression `base + size` on line 2. However, it could
 * also be something more complex like `(base, size)` where `base` is from line 3 and `size` is from line 2, and the
 * pointer-arithmetic instruction is `base + n` on line 3 in the following example:
 *  ```cpp
 *  1. int* base = new int[size];
 *  2. if(n <= size) {
 *  3.   int* end = base + n;
 *  4.   for(int* p = base; p <= end; ++p) {
 *  5.     *p = 0; // BUG: Should have been bounded by `p < end`.
 *  6.   }
 *  7. }
 *  ```
 *
 * Reducing the size of `pointerAddInstructionHasBounds`:
 * The `pointerAddInstructionHasBounds` can be very large since the `sink2` column is defined as anything that non-strictly
 * upper bounds the right-hand side of a pointer-arithmetic instruction. In order to reduce the size of this predicate we prune
 * the set of pointer-arithmetic instructions to only those instructions where the left-hand side flows from an allocation.
 *
 * Handling false positives:
 *
 * Consider a snippet such as:
 * ```cpp
 * 1. int* base = new int[size];
 * 2. int n = condition() ? size : 0;
 * 3. if(n >= size) return;
 * 4. int* end = base + n;
 * 5. for(int* p = base; p <= end; ++p) {
 * 6.   *p = 0; // This is fine since `end < base + size`
 * 7. }
 * ```
 * In order to remove this false positive we define a barrier (see `Barrier2::BarrierConfig2`) that finds the possible guards
 * that compares a value to the size of the allocation. In the above example, that's the `(n >= size)` guard on line 3.
 * `Barrier2::getABarrierNode` then defines any node that's guarded by such a guard as a barrier in the dataflow configuration.
 */

private import cpp
private import semmle.code.cpp.ir.dataflow.internal.ProductFlow
private import semmle.code.cpp.ir.ValueNumbering
private import semmle.code.cpp.controlflow.IRGuards
private import codeql.util.Unit
private import RangeAnalysisUtil

private VariableAccess getAVariableAccess(Expr e) { e.getAChild*() = result }

/**
 * Holds if the `(n, state)` pair represents the source of flow for the size
 * expression associated with `alloc`.
 */
predicate hasSize(HeuristicAllocationExpr alloc, DataFlow::Node n, int state) {
  exists(VariableAccess va, Expr size, int delta |
    size = alloc.getSizeExpr() and
    // Get the unique variable in a size expression like `x` in `malloc(x + 1)`.
    va = unique( | | getAVariableAccess(size)) and
    // Compute `delta` as the constant difference between `x` and `x + 1`.
    bounded1(any(Instruction instr | instr.getUnconvertedResultExpression() = size),
      any(LoadInstruction load | load.getUnconvertedResultExpression() = va), delta) and
    n.asConvertedExpr() = va.getFullyConverted() and
    state = delta
  )
}

/**
 * A module that encapsulates a barrier guard to remove false positives from flow like:
 * ```cpp
 * char *p = new char[size];
 * // ...
 * unsigned n = size;
 * // ...
 * if(n < size) {
 *   use(*p[n]);
 * }
 * ```
 * In this case, the sink pair identified by the product flow library (without any additional barriers)
 * would be `(p, n)` (where `n` is the `n` in `p[n]`), because there exists a pointer-arithmetic
 * instruction `pai` such that:
 * 1. The left-hand of `pai` flows from the allocation, and
 * 2. The right-hand of `pai` is non-strictly upper bounded by `n` (where `n` is the `n` in `p[n]`)
 * but because there's a strict comparison that compares `n` against the size of the allocation this
 * snippet is fine.
 */
module Barrier2 {
  private class FlowState2 = int;

  private module BarrierConfig2 implements DataFlow::ConfigSig {
    predicate isSource(DataFlow::Node source) {
      // The sources is the same as in the sources for the second
      // projection in the `AllocToInvalidPointerConfig` module.
      hasSize(_, source, _)
    }

    additional predicate isSink(
      DataFlow::Node left, DataFlow::Node right, IRGuardCondition g, FlowState2 state,
      boolean testIsTrue
    ) {
      // The sink is any "large" side of a relational comparison.
      g.comparesLt(left.asOperand(), right.asOperand(), state, true, testIsTrue)
    }

    predicate isSink(DataFlow::Node sink) { isSink(_, sink, _, _, _) }
  }

  private import DataFlow::Global<BarrierConfig2>

  private FlowState2 getAFlowStateForNode(DataFlow::Node node) {
    exists(DataFlow::Node source |
      flow(source, node) and
      hasSize(_, source, result)
    )
  }

  private predicate operandGuardChecks(
    IRGuardCondition g, Operand left, Operand right, FlowState2 state, boolean edge
  ) {
    exists(DataFlow::Node nLeft, DataFlow::Node nRight, FlowState2 state0 |
      nRight.asOperand() = right and
      nLeft.asOperand() = left and
      BarrierConfig2::isSink(nLeft, nRight, g, state0, edge) and
      state = getAFlowStateForNode(nRight) and
      state0 <= state
    )
  }

  /**
   * Gets an instruction that is guarded by a guard condition which ensures that
   * the value of the instruction is upper-bounded by size of some allocation.
   */
  Instruction getABarrierInstruction(FlowState2 state) {
    exists(IRGuardCondition g, ValueNumber value, Operand use, boolean edge |
      use = value.getAUse() and
      operandGuardChecks(pragma[only_bind_into](g), pragma[only_bind_into](use), _,
        pragma[only_bind_into](state), pragma[only_bind_into](edge)) and
      result = value.getAnInstruction() and
      g.controls(result.getBlock(), edge)
    )
  }

  /**
   * Gets a `DataFlow::Node` that is guarded by a guard condition which ensures that
   * the value of the node is upper-bounded by size of some allocation.
   */
  DataFlow::Node getABarrierNode(FlowState2 state) {
    result.asOperand() = getABarrierInstruction(state).getAUse()
  }

  /**
   * Gets the block of a node that is guarded (see `getABarrierInstruction` or
   * `getABarrierNode` for the definition of what it means to be guarded).
   */
  IRBlock getABarrierBlock(FlowState2 state) {
    result.getAnInstruction() = getABarrierInstruction(state)
  }
}

private module InterestingPointerAddInstruction {
  private module PointerAddInstructionConfig implements DataFlow::ConfigSig {
    predicate isSource(DataFlow::Node source) {
      // The sources is the same as in the sources for the second
      // projection in the `AllocToInvalidPointerConfig` module.
      hasSize(source.asConvertedExpr(), _, _)
    }

    predicate isSink(DataFlow::Node sink) {
      sink.asInstruction() = any(PointerAddInstruction pai).getLeft()
    }
  }

  private import DataFlow::Global<PointerAddInstructionConfig>

  /**
   * Holds if `pai` is a pointer-arithmetic instruction such that the
   * result of an allocation flows to the left-hand side of `pai`.
   *
   * This predicate is used to reduce the set of tuples in `isSinkPair`.
   */
  predicate isInteresting(PointerAddInstruction pai) {
    exists(DataFlow::Node n |
      n.asInstruction() = pai.getLeft() and
      flowTo(n)
    )
  }
}

/**
 * A product-flow configuration for flow from an `(allocation, size)` pair to a pointer-
 * arithmetic instruction that is non-strictly upper-bounded by `allocation + size`.
 */
private module Config implements ProductFlow::StateConfigSig {
  class FlowState1 = Unit;

  class FlowState2 = int;

  predicate isSourcePair(
    DataFlow::Node source1, FlowState1 state1, DataFlow::Node source2, FlowState2 state2
  ) {
    // In the case of an allocation like
    // ```cpp
    // malloc(size + 1);
    // ```
    // we use `state2` to remember that there was an offset (in this case an offset of `1`) added
    // to the size of the allocation. This state is then checked in `isSinkPair`.
    exists(state1) and
    hasSize(source1.asConvertedExpr(), source2, state2)
  }

  predicate isSinkPair(
    DataFlow::Node sink1, FlowState1 state1, DataFlow::Node sink2, FlowState2 state2
  ) {
    exists(state1) and
    // We check that the delta computed by the range analysis matches the
    // state value that we set in `isSourcePair`.
    pointerAddInstructionHasBounds0(_, sink1, sink2, state2)
  }

  predicate isBarrier2(DataFlow::Node node, FlowState2 state) {
    node = Barrier2::getABarrierNode(state)
  }

  predicate isBarrierIn1(DataFlow::Node node) { isSourcePair(node, _, _, _) }

  predicate isBarrierOut2(DataFlow::Node node) {
    node = any(DataFlow::SsaPhiNode phi).getAnInput(true)
  }
}

private module AllocToInvalidPointerFlow = ProductFlow::GlobalWithState<Config>;

/**
 * Holds if `pai` is non-strictly upper bounded by `sink2 + delta` and `sink1` is the
 * left operand of the pointer-arithmetic operation.
 *
 * For example in,
 * ```cpp
 * char* end = p + (size + 1);
 * ```
 * We will have:
 * - `pai` is `p + (size + 1)`,
 * - `sink1` is `p`
 * - `sink2` is `size`
 * - `delta` is `1`.
 */
pragma[nomagic]
private predicate pointerAddInstructionHasBounds0(
  PointerAddInstruction pai, DataFlow::Node sink1, DataFlow::Node sink2, int delta
) {
  InterestingPointerAddInstruction::isInteresting(pragma[only_bind_into](pai)) and
  exists(Instruction right, Instruction instr2 |
    pai.getRight() = right and
    pai.getLeft() = sink1.asInstruction() and
    instr2 = sink2.asInstruction() and
    // pai.getRight() <= sink2 + delta
    bounded1(right, instr2, delta) and
    not right = Barrier2::getABarrierInstruction(delta) and
    not instr2 = Barrier2::getABarrierInstruction(delta)
  )
}

/**
 * Holds if `allocation` flows to `sink1` and `sink1` represents the left-hand
 * side of the pointer-arithmetic instruction `pai`, and the right-hand side of `pai`
 * is non-strictly upper bounded by the size of `alllocation` + `delta`.
 */
pragma[nomagic]
predicate pointerAddInstructionHasBounds(
  DataFlow::Node allocation, PointerAddInstruction pai, DataFlow::Node sink1, int delta
) {
  exists(DataFlow::Node sink2 |
    AllocToInvalidPointerFlow::flow(allocation, _, sink1, sink2) and
    pointerAddInstructionHasBounds0(pai, sink1, sink2, delta)
  )
}
