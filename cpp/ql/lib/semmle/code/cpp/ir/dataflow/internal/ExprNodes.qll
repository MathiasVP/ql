/**
 * Provides the classes `ExprNode` and `IndirectExprNode` for converting between `Expr` and `Node`.
 */

private import cpp
private import semmle.code.cpp.ir.IR
private import DataFlowUtil
private import DataFlowPrivate
private import DataFlowNodes
private import semmle.code.cpp.ir.implementation.raw.internal.IRConstruction as IRConstruction

cached
private module Cached {
  private Operand getAnInitializeDynamicAllocationInstructionAddress() {
    result = any(InitializeDynamicAllocationInstruction init).getAllocationAddressOperand()
  }

  /**
   * Gets the expression that should be returned as the result expression from `instr`.
   *
   * Note that this predicate may return multiple results in cases where a conversion belongs to a
   * different AST element than its operand.
   */
  private Expr getConvertedResultExpression(Instruction instr, int n) {
    // Only fully converted instructions have a result for `asConvertedExpr`
    not conversionFlow(unique(Operand op |
        // The address operand of a `InitializeDynamicAllocationInstruction` is
        // special: we need to handle it during dataflow (since it's
        // effectively a store to an indirection), but it doesn't appear in
        // source syntax, so dataflow node <-> expression conversion shouldn't
        // care about it.
        op = getAUse(instr) and not op = getAnInitializeDynamicAllocationInstructionAddress()
      |
        op
      ), _, false, false) and
    result = getConvertedResultExpressionImpl(instr) and
    n = 0
    or
    // If the conversion also has a result then we return multiple results
    exists(Operand operand | conversionFlow(operand, instr, false, false) |
      n = 1 and
      result = getConvertedResultExpressionImpl(operand.getDef())
      or
      result = getConvertedResultExpression(operand.getDef(), n - 1)
    )
  }

  private Expr getRankedElementExpr(ArrayAggregateLiteral aggr, int rnk) {
    result =
      rank[rnk + 1](Expr e, int elementIndex, int position |
        e = aggr.getElementExpr(elementIndex, position)
      |
        e order by elementIndex, position
      )
  }

  private class LastArrayAggregateStore extends StoreInstruction {
    ArrayAggregateLiteral aggr;

    LastArrayAggregateStore() {
      exists(int rnk |
        this.getSourceValue().getUnconvertedResultExpression() = getRankedElementExpr(aggr, rnk) and
        not exists(getRankedElementExpr(aggr, rnk + 1))
      )
    }

    ArrayAggregateLiteral getArrayAggregateLiteral() { result = aggr }
  }

  private Expr getConvertedResultExpressionImpl0(Instruction instr) {
    // IR construction inserts an additional cast to a `size_t` on the extent
    // of a `new[]` expression. The resulting `ConvertInstruction` doesn't have
    // a result for `getConvertedResultExpression`. We remap this here so that
    // this `ConvertInstruction` maps to the result of the expression that
    // represents the extent.
    result = IRConstruction::Raw::getAllocationExtentConvertExpr(instr)
    or
    result = IRConstruction::Raw::getTransparentConversionParenthesisExpr(instr)
    or
    // Certain expressions generate `CopyValueInstruction`s only when they
    // are needed. Examples of this include crement operations and compound
    // assignment operations. For example:
    // ```cpp
    // int x = ...
    // int y = x++;
    // ```
    // this generate IR like:
    // ```
    // r1(glval<int>) = VariableAddress[x] :
    // r2(int)        = Constant[0]        :
    // m3(int)        = Store[x]           : &:r1, r2
    // r4(glval<int>) = VariableAddress[y] :
    // r5(glval<int>) = VariableAddress[x] :
    // r6(int)        = Load[x]            : &:r5, m3
    // r7(int)        = Constant[1]        :
    // r8(int)        = Add                : r6, r7
    // m9(int)        = Store[x]           : &:r5, r8
    // r11(int)       = CopyValue         : r6
    // m12(int)       = Store[y]          : &:r4, r11
    // ```
    // When the `CopyValueInstruction` is not generated there is no instruction
    // whose `getConvertedResultExpression` maps back to the expression. When
    // such an instruction doesn't exist it means that the old value is not
    // needed, and in that case the only value that will propagate forward in
    // the program is the value that's been updated. So in those cases we just
    // use the result of `node.asDefinition()` as the result of `node.asExpr()`.
    exists(StoreInstruction store |
      store = instr and
      IRConstruction::Raw::instructionProducesExprResult(store) and
      result = asDefinitionImpl0(store)
    )
    or
    // IR construction breaks an array aggregate literal `{1, 2, 3}` into a
    // sequence of `StoreInstruction`s. So there's no instruction `i` for which
    // `i.getUnconvertedResultExpression() instanceof ArrayAggregateLiteral`.
    // So we map the instruction node corresponding to the last `Store`
    // instruction of the sequence to the result of the array aggregate
    // literal. This makes sense since this store will immediately flow into
    // the indirect node representing the array. So this node does represent
    // the array after it has been fully initialized.
    result = instr.(LastArrayAggregateStore).getArrayAggregateLiteral()
  }

  private Expr getConvertedResultExpressionImpl(Instruction instr) {
    result = getConvertedResultExpressionImpl0(instr)
    or
    not exists(getConvertedResultExpressionImpl0(instr)) and
    result = instr.getConvertedResultExpression()
  }

  /**
   * Gets the result for `node.asDefinition()` (when `node` is the instruction
   * node that wraps `store`) in the cases where `store.getAst()` should not be
   * used to define the result of `node.asDefinition()`.
   */
  private Expr asDefinitionImpl0(StoreInstruction store) {
    // For an expression such as `i += 2` we pretend that the generated
    // `StoreInstruction` contains the result of the expression even though
    // this isn't totally aligned with the C/C++ standard.
    result = IRConstruction::Raw::getAssignOperationStoreExpr(store)
    or
    result = IRConstruction::Raw::getCrementOperationStoreExpr(store)
  }

  /**
   * Holds if the expression returned by `store.getAst()` should not be
   * returned as the result of `node.asDefinition()` when `node` is the
   * instruction node that wraps `store`.
   */
  private predicate excludeAsDefinitionResult(StoreInstruction store) {
    // Exclude the store to the temporary generated by a ternary expression.
    IRConstruction::Raw::isConditionalExprTempStore(store)
  }

  /**
   * Gets the expression that represents the result of `StoreInstruction` for
   * dataflow purposes.
   *
   * For example, consider the following example
   * ```cpp
   * int x = 42;     // 1
   * x = 34;         // 2
   * ++x;            // 3
   * x++;            // 4
   * x += 1;         // 5
   * int y = x += 2; // 6
   * ```
   * For (1) the result is `42`.
   * For (2) the result is `x = 34`.
   * For (3) the result is `++x`.
   * For (4) the result is `x++`.
   * For (5) the result is `x += 1`.
   * For (6) there are two results:
   *   - For the `StoreInstruction` generated by `x += 2` the result
   *     is `x += 2`
   *   - For the `StoreInstruction` generated by `int y = ...` the result
   *     is also `x += 2`
   */
  cached
  Expr asDefinitionImpl(StoreInstruction store) {
    not exists(asDefinitionImpl0(store)) and
    not excludeAsDefinitionResult(store) and
    result = store.getAst().(Expr).getUnconverted()
    or
    result = asDefinitionImpl0(store)
  }

  /**
   * Gets the instruction that computes the `n`'th expression in the conversion
   * chain of `instr` (see `getConvertedResultExpression`).
   */
  private Instruction getConvertedResultInstruction(Instruction instr, int n) {
    result = instr and n = 0
    or
    exists(Operand operand | conversionFlow(operand, instr, false, false) |
      result = getConvertedResultInstruction(operand.getDef(), n - 1)
    )
  }

  /** Holds if `node` is an `OperandNode` that should map `node.asExpr()` to `e`. */
  private predicate exprNodeShouldBeOperand(OperandNode node, Expr e, int n) {
    not exprNodeShouldBeIndirectOperand(_, e, n, _) and
    exists(Instruction def |
      getExprOperand(def) = node.getOperand() and
      exprHasIndirection(def, e, n, 0)
    )
  }

  /** Holds if `node` should be an `IndirectOperand` that maps `node.asIndirectExpr()` to `e`. */
  private predicate indirectExprNodeShouldBeIndirectOperand(
    IndirectOperand node, Expr e, int n, int indirectionIndex, int ind
  ) {
    exists(Instruction def, int nodeIndex |
      node.hasOperandAndIndirectionIndex(getExprOperand(def), nodeIndex) and
      exprHasIndirection(def, e, n, ind) and
      indirectionIndex = nodeIndex - ind + getArrayDecayAdjustment(e, ind) and
      indirectionIndex > 0
    )
  }

  /** Holds if `operand`'s definition is a `VariableAddressInstruction` whose variable is a temporary */
  private predicate isIRTempVariable(Operand operand) {
    operand.getDef().(VariableAddressInstruction).getIRVariable() instanceof IRTempVariable
  }

  /**
   * Holds if `e` is the `n`'th expression in the conversion chain of `def`, and
   * the value of `e` is obtained after `ind` number of loads from the result of
   * `def`.
   *
   * The instruction that computes an expression that denotes an object (for
   * example, the qualifier `x` in `x.f()`) produces the address of the object,
   * and likewise for an expression of reference type. So the value of such an
   * expression is obtained after one load.
   */
  private predicate exprHasIndirection(Instruction def, Expr e, int n, int ind) {
    exists(int ind0 |
      e = getConvertedResultExpression(def, n) and
      if
        (getConvertedResultInstruction(def, n).isGLValue() or isReferenceExpr(e)) and
        not e.getUnspecifiedType() instanceof RoutineType
      then ind0 = 1
      else ind0 = 0
    |
      // The dataflow library treats an array value as a pointer to its
      // elements, so the elements of an array that is loaded as a whole are
      // behind one additional indirection.
      if ind0 = 1 and e.getUnspecifiedType() instanceof ArrayType and isLoadedArray(def)
      then ind = 2
      else ind = ind0
    )
  }

  /**
   * Holds if `e` has reference type and denotes the object it refers to. A
   * `ReferenceToExpr` takes the address of its operand to bind a reference.
   */
  private predicate isReferenceExpr(Expr e) {
    e.getUnspecifiedType() instanceof ReferenceType and
    not e instanceof ReferenceToExpr
  }

  /**
   * Holds if `def` computes the address of an array that is loaded as a whole,
   * as in `char buf[] = "abc"`.
   */
  private predicate isLoadedArray(Instruction def) {
    exists(LoadInstruction load, Type t |
      load.getSourceAddressOperand() = getExprOperand(def) and
      load.getResultLanguageType().hasType(t, false) and
      t.getUnspecifiedType() instanceof ArrayType
    )
  }

  /**
   * Gets `1` if `e` is an array whose value is obtained after `ind > 0` loads,
   * and `0` otherwise. Dereferencing an array first converts it to a pointer to
   * its first element, so `*buf` is the contents of `buf` (just like `buf`).
   */
  bindingset[e, ind]
  private int getArrayDecayAdjustment(Expr e, int ind) {
    if ind > 0 and e.getUnspecifiedType() instanceof ArrayType then result = 1 else result = 0
  }

  /**
   * Gets the operand that uses the result of `def`. When a prvalue argument is
   * bound to a reference parameter IR construction introduces a temporary
   * whose address is used both to initialize it and as the argument.
   */
  private Operand getExprOperand(Instruction def) {
    result = unique( | | getAUse(def))
    or
    not exists(unique( | | getAUse(def))) and
    result = unique(ArgumentOperand arg | arg = getAUse(def)) and
    isIRTempVariable(result)
  }

  /** Holds if `node` should be an `IndirectOperand` that maps `node.asExpr()` to `e`. */
  private predicate exprNodeShouldBeIndirectOperand(IndirectOperand node, Expr e, int n, int ind) {
    exists(Instruction def |
      ind > 0 and
      node.hasOperandAndIndirectionIndex(getExprOperand(def), ind) and
      exprHasIndirection(def, e, n, ind)
    )
  }

  private predicate exprNodeShouldBeIndirectOutNode(IndirectArgumentOutNode node, Expr e, int n) {
    exists(CallInstruction call |
      call.getStaticCallTarget() instanceof Constructor and
      e = getConvertedResultExpression(call, n) and
      call.getThisArgumentOperand() = node.getAddressOperand() and
      // Indirection index 0 is the `this` pointer, and 1 is the constructed object
      node.getIndirectionIndex() = 1
    )
  }

  /** Holds if `node` should be an instruction node that maps `node.asExpr()` to `e`. */
  private predicate exprNodeShouldBeInstruction(Node node, Expr e, int n) {
    not exprNodeShouldBeOperand(_, e, n) and
    not exprNodeShouldBeIndirectOutNode(_, e, n) and
    not exprNodeShouldBeIndirectOperand(_, e, n, _) and
    exprHasIndirection(node.asInstruction(), e, n, 0)
  }

  /**
   * The IR doesn't have an instruction `i` for which this holds:
   * ```
   * i.getUnconvertedResultExpression() instanceof ClassAggregateLiteral
   * ```
   * and thus we don't automatically get a dataflow node for which:
   * ```
   * node.asExpr() instanceof ClassAggregateLiteral
   * ```
   * This is because the IR represents a `ClassAggregateLiteral` as a sequence
   * of field writes. To work around this we map `asExpr` on the
   * `PostUpdateNode` for the last field write to the class aggregate literal.
   */
  private class ClassAggregateInitializerPostUpdateNode extends PostFieldUpdateNode {
    ClassAggregateLiteral aggr;

    ClassAggregateInitializerPostUpdateNode() {
      exists(Node node1, FieldContent fc, int position, StoreInstruction store |
        store.getSourceValue().getUnconvertedResultExpression() =
          aggr.getFieldExpr(fc.getField(), position) and
        node1.asInstruction() = store and
        // This is the last field write from the aggregate initialization.
        not exists(aggr.getFieldExpr(_, position + 1)) and
        storeStep(node1, fc, this)
      )
    }

    ClassAggregateLiteral getClassAggregateLiteral() { result = aggr }
  }

  private predicate exprNodeShouldBePostUpdateNode(Node node, Expr e, int n) {
    node.(ClassAggregateInitializerPostUpdateNode).getClassAggregateLiteral() = e and
    n = 0
  }

  /** Holds if `node` should be an `IndirectInstruction` that maps `node.asExpr()` to `e`. */
  private predicate exprNodeShouldBeIndirectInstruction(
    IndirectInstruction node, Expr e, int n, int ind
  ) {
    not exprNodeShouldBeOperand(_, e, n) and
    not exprNodeShouldBeIndirectOutNode(_, e, n) and
    not exprNodeShouldBeIndirectOperand(_, e, n, _) and
    exists(Instruction def |
      ind > 0 and
      node.hasInstructionAndIndirectionIndex(def, ind) and
      exprHasIndirection(def, e, n, ind)
    )
  }

  /** Holds if `node` should be an `IndirectInstruction` that maps `node.asIndirectExpr()` to `e`. */
  private predicate indirectExprNodeShouldBeIndirectInstruction(
    IndirectInstruction node, Expr e, int n, int indirectionIndex, int ind
  ) {
    not indirectExprNodeShouldBeIndirectOperand(_, e, n, indirectionIndex, _) and
    exists(Instruction instr, int nodeIndex |
      node.hasInstructionAndIndirectionIndex(instr, nodeIndex) and
      exprHasIndirection(instr, e, n, ind) and
      indirectionIndex = nodeIndex - ind + getArrayDecayAdjustment(e, ind) and
      indirectionIndex > 0
    )
  }

  abstract private class ExprNodeBase extends Node {
    /**
     * Holds if `e` is the `n`'th expression corresponding to this node, and the
     * value of `e` is obtained after `ind` number of loads. The expression may
     * be a `Conversion`.
     */
    abstract predicate hasConvertedExpr(Expr e, int n, int ind);

    /**
     * Gets the expression corresponding to this node, if any. The returned
     * expression may be a `Conversion`.
     */
    final Expr getConvertedExpr(int n) { this.hasConvertedExpr(result, n, _) }

    /** Gets the non-conversion expression corresponding to this node, if any. */
    final Expr getExpr(int n) {
      exists(Expr e, int ind |
        this.hasConvertedExpr(e, n, ind) and
        result = e.getUnconverted() and
        isLeastConvertedIndirection(result, ind)
      )
    }
  }

  /**
   * Holds if there exists a dataflow node whose `asExpr(n)` should evaluate
   * to `e`, and the value of `e` is obtained after `ind` number of loads.
   */
  private predicate exprNodeShouldBe(Expr e, int n, int ind) {
    (
      exprNodeShouldBeInstruction(_, e, n) or
      exprNodeShouldBeOperand(_, e, n) or
      exprNodeShouldBeIndirectOutNode(_, e, n) or
      exprNodeShouldBePostUpdateNode(_, e, n)
    ) and
    ind = 0
    or
    exprNodeShouldBeIndirectOperand(_, e, n, ind)
    or
    exprNodeShouldBeIndirectInstruction(_, e, n, ind)
  }

  pragma[nomagic]
  private predicate unconvertedExprNodeShouldBe(Expr u, int n, int ind) {
    exists(Expr e | exprNodeShouldBe(e, n, ind) and u = e.getUnconverted())
  }

  /**
   * Holds if the value of the least converted expression whose unconverted
   * expression is `u` is obtained after `ind` number of loads. For example, if
   * `buf` is an array then its array-to-pointer conversion maps to the pointer,
   * but `buf` itself maps to the contents of `buf`.
   */
  private predicate isLeastConvertedIndirection(Expr u, int ind) {
    exists(int n |
      unconvertedExprNodeShouldBe(u, n, ind) and
      not unconvertedExprNodeShouldBe(u, n + 1, _)
    )
  }

  private class InstructionExprNode extends ExprNodeBase, InstructionNode {
    InstructionExprNode() {
      exists(Expr e, int n |
        exprNodeShouldBeInstruction(this, e, n) and
        not unconvertedExprNodeShouldBe(e.getUnconverted(), n + 1, 0)
      )
    }

    final override predicate hasConvertedExpr(Expr e, int n, int ind) {
      exprNodeShouldBeInstruction(this, e, n) and ind = 0
    }
  }

  private class OperandExprNode extends ExprNodeBase, OperandNode {
    OperandExprNode() {
      exists(Expr e, int n |
        exprNodeShouldBeOperand(this, e, n) and
        not unconvertedExprNodeShouldBe(e.getUnconverted(), n + 1, 0)
      )
    }

    final override predicate hasConvertedExpr(Expr e, int n, int ind) {
      exprNodeShouldBeOperand(this, e, n) and ind = 0
    }
  }

  abstract private class IndirectExprNodeBase extends Node {
    /**
     * Holds if `e` is the `n`'th expression corresponding to this node after
     * `indirectionIndex` number of indirections, and the value of `e` is
     * obtained after `ind` number of loads. The expression may be a `Conversion`.
     */
    abstract predicate hasConvertedExpr(Expr e, int n, int indirectionIndex, int ind);

    /**
     * Gets the expression corresponding to this node, if any. The returned
     * expression may be a `Conversion`.
     */
    final Expr getConvertedExpr(int n, int indirectionIndex) {
      this.hasConvertedExpr(result, n, indirectionIndex, _)
    }

    /** Gets the non-conversion expression corresponding to this node, if any. */
    final Expr getExpr(int n, int indirectionIndex) {
      exists(Expr e, int ind |
        this.hasConvertedExpr(e, n, indirectionIndex, ind) and
        result = e.getUnconverted() and
        isLeastConvertedIndirection(result, ind)
      )
    }
  }

  /** A signature for converting an indirect node to an expression. */
  private signature module IndirectNodeToIndirectExprSig {
    /** The indirect node class to be converted to an expression */
    class IndirectNode;

    /**
     * Holds if the indirect expression at indirection index `indirectionIndex`
     * of `node` is `e`. The integer `n` specifies how many conversions has been
     * applied to `node`, and the value of `e` is obtained after `ind` loads.
     */
    predicate indirectNodeHasIndirectExpr(
      IndirectNode node, Expr e, int n, int indirectionIndex, int ind
    );
  }

  /**
   * A module that implements the logic for deciding whether an indirect node
   * should be an `IndirectExprNode`.
   */
  private module IndirectNodeToIndirectExpr<IndirectNodeToIndirectExprSig Sig> {
    import Sig

    /**
     * This predicate shifts the indirection index by one when `conv` is a
     * `ReferenceDereferenceExpr`.
     *
     * This is necessary because `ReferenceDereferenceExpr` is a conversion
     * in the AST, but appears as a `LoadInstruction` in the IR.
     */
    bindingset[e, indirectionIndex]
    private predicate adjustForReference(
      Expr e, int indirectionIndex, Expr conv, int adjustedIndirectionIndex
    ) {
      conv.(ReferenceDereferenceExpr).getExpr() = e and
      adjustedIndirectionIndex = indirectionIndex - 1
      or
      not conv instanceof ReferenceDereferenceExpr and
      conv = e and
      adjustedIndirectionIndex = indirectionIndex
    }

    /** Holds if `node` should be an `IndirectExprNode`. */
    predicate charpred(IndirectNode node) {
      exists(Expr e, int n, int indirectionIndex, int ind |
        indirectNodeHasIndirectExpr(node, e, n, indirectionIndex, ind) and
        not exists(Expr conv, int adjustedIndirectionIndex |
          adjustForReference(e, indirectionIndex, conv, adjustedIndirectionIndex) and
          indirectExprNodeShouldBe(conv, n + 1, adjustedIndirectionIndex, ind)
        )
      )
    }
  }

  private predicate indirectExprNodeShouldBe(Expr e, int n, int indirectionIndex, int ind) {
    indirectExprNodeShouldBeIndirectOperand(_, e, n, indirectionIndex, ind) or
    indirectExprNodeShouldBeIndirectInstruction(_, e, n, indirectionIndex, ind)
  }

  private module IndirectOperandIndirectExprNodeImpl implements IndirectNodeToIndirectExprSig {
    class IndirectNode = IndirectOperand;

    predicate indirectNodeHasIndirectExpr = indirectExprNodeShouldBeIndirectOperand/5;
  }

  module IndirectOperandToIndirectExpr =
    IndirectNodeToIndirectExpr<IndirectOperandIndirectExprNodeImpl>;

  private class IndirectOperandIndirectExprNode extends IndirectExprNodeBase instanceof IndirectOperand
  {
    IndirectOperandIndirectExprNode() { IndirectOperandToIndirectExpr::charpred(this) }

    final override predicate hasConvertedExpr(Expr e, int n, int index, int ind) {
      IndirectOperandToIndirectExpr::indirectNodeHasIndirectExpr(this, e, n, index, ind)
    }
  }

  private module IndirectInstructionIndirectExprNodeImpl implements IndirectNodeToIndirectExprSig {
    class IndirectNode = IndirectInstruction;

    predicate indirectNodeHasIndirectExpr = indirectExprNodeShouldBeIndirectInstruction/5;
  }

  module IndirectInstructionToIndirectExpr =
    IndirectNodeToIndirectExpr<IndirectInstructionIndirectExprNodeImpl>;

  private class IndirectInstructionIndirectExprNode extends IndirectExprNodeBase instanceof IndirectInstruction
  {
    IndirectInstructionIndirectExprNode() { IndirectInstructionToIndirectExpr::charpred(this) }

    final override predicate hasConvertedExpr(Expr e, int n, int index, int ind) {
      IndirectInstructionToIndirectExpr::indirectNodeHasIndirectExpr(this, e, n, index, ind)
    }
  }

  private class IndirectArgumentOutExprNode extends ExprNodeBase, IndirectArgumentOutNode {
    IndirectArgumentOutExprNode() { exprNodeShouldBeIndirectOutNode(this, _, _) }

    final override predicate hasConvertedExpr(Expr e, int n, int ind) {
      exprNodeShouldBeIndirectOutNode(this, e, n) and ind = 0
    }
  }

  private class IndirectOperandExprNode extends ExprNodeBase instanceof IndirectOperand {
    IndirectOperandExprNode() {
      exists(Expr e, int n, int ind |
        exprNodeShouldBeIndirectOperand(this, e, n, ind) and
        not unconvertedExprNodeShouldBe(e.getUnconverted(), n + 1, ind)
      )
    }

    final override predicate hasConvertedExpr(Expr e, int n, int ind) {
      exprNodeShouldBeIndirectOperand(this, e, n, ind)
    }
  }

  private class IndirectInstructionExprNode extends ExprNodeBase instanceof IndirectInstruction {
    IndirectInstructionExprNode() {
      exists(Expr e, int n, int ind |
        exprNodeShouldBeIndirectInstruction(this, e, n, ind) and
        not unconvertedExprNodeShouldBe(e.getUnconverted(), n + 1, ind)
      )
    }

    final override predicate hasConvertedExpr(Expr e, int n, int ind) {
      exprNodeShouldBeIndirectInstruction(this, e, n, ind)
    }
  }

  private class PostUpdateExprNode extends ExprNodeBase instanceof PostUpdateNode {
    PostUpdateExprNode() { exprNodeShouldBePostUpdateNode(this, _, _) }

    final override predicate hasConvertedExpr(Expr e, int n, int ind) {
      exprNodeShouldBePostUpdateNode(this, e, n) and ind = 0
    }
  }

  /**
   * An expression, viewed as a node in a data flow graph.
   */
  cached
  class ExprNode extends Node instanceof ExprNodeBase {
    /**
     * INTERNAL: Do not use.
     */
    cached
    Expr getExpr(int n) { result = super.getExpr(n) }

    /**
     * Gets the non-conversion expression corresponding to this node, if any. If
     * this node strictly (in the sense of `getConvertedExpr`) corresponds to a
     * `Conversion`, then the result is that `Conversion`'s non-`Conversion` base
     * expression.
     */
    cached
    final Expr getExpr() { result = this.getExpr(_) }

    /**
     * INTERNAL: Do not use.
     */
    cached
    Expr getConvertedExpr(int n) { result = super.getConvertedExpr(n) }

    /**
     * Gets the expression corresponding to this node, if any. The returned
     * expression may be a `Conversion`.
     */
    cached
    final Expr getConvertedExpr() { result = this.getConvertedExpr(_) }
  }

  /**
   * An indirect expression, viewed as a node in a data flow graph.
   */
  cached
  class IndirectExprNode extends Node instanceof IndirectExprNodeBase {
    /**
     * Gets the non-conversion expression corresponding to this node, if any. If
     * this node strictly (in the sense of `getConvertedExpr`) corresponds to a
     * `Conversion`, then the result is that `Conversion`'s non-`Conversion` base
     * expression.
     */
    cached
    final Expr getExpr(int indirectionIndex) { result = this.getExpr(_, indirectionIndex) }

    /**
     * INTERNAL: Do not use.
     */
    cached
    Expr getExpr(int n, int indirectionIndex) { result = super.getExpr(n, indirectionIndex) }

    /**
     * INTERNAL: Do not use.
     */
    cached
    Expr getConvertedExpr(int n, int indirectionIndex) {
      result = super.getConvertedExpr(n, indirectionIndex)
    }

    /**
     * Gets the expression corresponding to this node, if any. The returned
     * expression may be a `Conversion`.
     */
    cached
    Expr getConvertedExpr(int indirectionIndex) {
      result = this.getConvertedExpr(_, indirectionIndex)
    }
  }
}

import Cached
