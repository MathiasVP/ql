/**
 * Provides C++-specific definitions for use in the data flow library.
 */

private import cpp
// The `ValueNumbering` library has to be imported right after `cpp` to ensure
// that the cached IR gets the same checksum here as it does in queries that use
// `ValueNumbering` without `DataFlow`.
private import semmle.code.cpp.ir.ValueNumbering
private import semmle.code.cpp.ir.IR
private import semmle.code.cpp.controlflow.IRGuards
private import semmle.code.cpp.models.interfaces.DataFlow
private import DataFlowPrivate
private import ModelUtil
private import semmle.code.cpp.ir.internal.IRCppLanguage as IRCppLanguage
private import SsaInternals as Ssa

cached
private module Cached {
  /**
   * The IR dataflow graph consists of the following nodes:
   * - `InstructionNode`, which represents an `Instruction` in the graph.
   * - `OperandNode`, which represents an `Operand` in the graph.
   * - `VariableNode`, which is used to model global variables.
   * - Two kinds of `StoreNode`s:
   *   1. `StoreNodeInstr`, which represents the value of an address computed by an `Instruction` that
   *      has been updated by a write operation.
   *   2. `StoreNodeOperand`, which represents the value of an address in an `ArgumentOperand` after a
   *      function call that may have changed the value.
   * - `ReadNode`, which represents the result of reading a field of an object.
   * - `SsaPhiNode`, which represents phi nodes as computed by the shared SSA library.
   *
   * The following section describes how flow is generally transferred between these nodes:
   * - Flow between `InstructionNode`s and `OperandNode`s follow the def-use information as computed by
   *   the IR. Because the IR compute must-alias information for memory operands, we only follow def-use
   *   flow for register operands.
   * - Flow can enter a `StoreNode` in two ways (both done in `StoreNode.flowInto`):
   *   1. Flow is transferred from a `StoreValueOperand` to a `StoreNodeInstr`. Flow will then proceed
   *      along the chain of addresses computed by `StoreNodeInstr.getInner` to identify field writes
   *      and call `storeStep` accordingly (i.e., for an expression like `a.b.c = x`, we visit `c`, then
   *      `b`, then `a`).
   *   2. Flow is transfered from a `WriteSideEffectInstruction` to a `StoreNodeOperand` after flow
   *      returns to a caller. Flow will then proceed to the defining instruction of the operand (because
   *      the `StoreNodeInstr` computed by `StoreNodeOperand.getInner()` is the `StoreNode` containing
   *      the defining instruction), and then along the chain computed by `StoreNodeInstr.getInner` like
   *      above.
   *   In both cases, flow leaves a `StoreNode` once the entire chain has been traversed, and the shared
   *   SSA library is used to find the next use of the variable at the end of the chain.
   * - Flow can enter a `ReadNode` through an `OperandNode` that represents an address of some variable.
   *   Flow will then proceed along the chain of addresses computed by `ReadNode.getOuter` (i.e., for an
   *   expression like `use(a.b.c)` we visit `a`, then `b`, then `c`) and call `readStep` accordingly.
   *   Once the entire chain has been traversed, flow is transferred to the load instruction that reads
   *   the final address of the chain.
   * - Flow can enter a `SsaPhiNode` from an `InstructionNode`, a `StoreNode` or another `SsaPhiNode`
   *   (in `toPhiNode`), depending on which node provided the previous definition of the underlying
   *   variable. Flow leaves a `SsaPhiNode` (in `fromPhiNode`) by using the shared SSA library to
   *   determine the next use of the variable.
   */
  cached
  newtype TIRDataFlowNode =
    TInstructionNode(Instruction i) or
    TOperandNode(Operand op) or
    TVariableNode(Variable var) or
    TPostFieldUpdateNode(Ssa::Def def, FieldAddress fieldAddress) {
      not ignoreOperand(fieldAddress) and
      isPostFieldUpdateNode(def, fieldAddress)
    } or
    TSsaPhiNode(Ssa::PhiNode phi) or
    TIndirectArgumentOutNode(Ssa::CallDef callDef) or
    TIndirectOperand(Operand op, int index) {
      exists(IRCppLanguage::CppType type, int m |
        not ignoreOperand(op) and
        type = Ssa::getLanguageType(op) and
        m = Ssa::countIndirectionsForCppType(type) and
        index = [1 .. m]
      )
    } or
    TIndirectInstruction(Instruction instr, int index) {
      exists(IRCppLanguage::CppType type, int m |
        not ignoreInstruction(instr) and
        type = Ssa::getResultLanguageType(instr) and
        m = Ssa::countIndirectionsForCppType(type) and
        index = [1 .. m]
      )
    }

  cached
  predicate localFlowStepCached(Node nodeFrom, Node nodeTo) {
    simpleLocalFlowStep(nodeFrom, nodeTo)
  }
}

predicate ignoreOperand(Operand operand) {
  operand = any(Instruction instr | ignoreInstruction(instr)).getAnOperand()
}

private predicate ignoreInstruction(Instruction instr) {
  instr instanceof WriteSideEffectInstruction or
  instr instanceof PhiInstruction or
  instr instanceof ReadSideEffectInstruction or
  instr instanceof ChiInstruction or
  instr instanceof InitializeIndirectionInstruction
}

class FieldAddress extends Operand {
  FieldAddressInstruction fai;

  FieldAddress() { fai = this.getDef() }

  Field getField() { result = fai.getField() }

  Instruction getObjectAddress() { result = fai.getObjectAddress() }

  Operand getObjectAddressOperand() { result = fai.getObjectAddressOperand() }

  Operand getAUse() { result = fai.getAUse() }
}

private predicate conversionFlow0(Operand opFrom, Operand opTo) {
  opTo.getDef().(CopyValueInstruction).getSourceValueOperand() = opFrom
  or
  opTo.getDef().(ConvertInstruction).getUnaryOperand() = opFrom
  or
  opTo.getDef().(CheckedConvertOrNullInstruction).getUnaryOperand() = opFrom
  or
  opTo.getDef().(InheritanceConversionInstruction).getUnaryOperand() = opFrom
  or
  opTo.getDef().(PointerArithmeticInstruction).getLeftOperand() = opFrom
}

predicate conversionFlow(Operand opFrom, Operand opTo, boolean hasFieldOffset) {
  hasFieldOffset = false and
  conversionFlow0(opFrom, opTo)
  or
  exists(FieldAddress fa |
    opTo = fa and
    opFrom = fa.getObjectAddressOperand() and
    hasFieldOffset = true
  )
}

predicate conversionFlowStepExcludeFields(Operand opFrom, Operand opTo) {
  conversionFlow(opFrom, opTo, false)
}

private predicate conversionFlowStepExcludeFieldsIncludeLoads(Operand opFrom, Operand opTo) {
  conversionFlowStepExcludeFields(opFrom, opTo)
  or
  opTo.getDef().(LoadInstruction).getSourceAddressOperand() = opFrom
}

private predicate conversionFlowStepIncludeLoads(Operand opFrom, Operand opTo) {
  conversionFlow(opFrom, opTo, _)
  or
  opTo.getDef().(LoadInstruction).getSourceAddressOperand() = opFrom
}

private predicate isPostFieldUpdateNode(Ssa::Def def, FieldAddress fieldAddress) {
  conversionFlowStepIncludeLoads*(fieldAddress, def.getAddressOperand())
}

/**
 * Holds if `operand` is a qualifier (skipping conversions and loads) of `fa2`.
 */
predicate isQualifierFor(Operand operand, FieldAddress fa2) {
  conversionFlowStepExcludeFieldsIncludeLoads*(operand, fa2.getObjectAddressOperand())
}

/**
 * INTERNAL: Do not use.
 */
module ToStringUtils {
  string stars() { result = "*****" }
}

private import Cached

/**
 * A node in a data flow graph.
 *
 * A node can be either an expression, a parameter, or an uninitialized local
 * variable. Such nodes are created with `DataFlow::exprNode`,
 * `DataFlow::parameterNode`, and `DataFlow::uninitializedNode` respectively.
 */
class Node extends TIRDataFlowNode {
  /**
   * INTERNAL: Do not use.
   */
  Declaration getEnclosingCallable() { none() } // overridden in subclasses

  /** Gets the function to which this node belongs, if any. */
  Function getFunction() { none() } // overridden in subclasses

  /** Gets the type of this node. */
  IRType getType() { none() } // overridden in subclasses

  /** Gets the instruction corresponding to this node, if any. */
  Instruction asInstruction() { result = this.(InstructionNode).getInstruction() }

  /** Gets the operands corresponding to this node, if any. */
  Operand asOperand() { result = this.(OperandNode).getOperand() }

  /**
   * Gets the non-conversion expression corresponding to this node, if any.
   * This predicate only has a result on nodes that represent the value of
   * evaluating the expression. For data flowing _out of_ an expression, like
   * when an argument is passed by reference, use `asDefiningArgument` instead
   * of `asExpr`.
   *
   * If this node strictly (in the sense of `asConvertedExpr`) corresponds to
   * a `Conversion`, then the result is the underlying non-`Conversion` base
   * expression.
   */
  Expr asExpr() { result = this.(ExprNode).getExpr() }

  /**
   * Gets the expression corresponding to this node, if any. The returned
   * expression may be a `Conversion`.
   */
  Expr asConvertedExpr() { result = this.(ExprNode).getConvertedExpr() }

  /**
   * Gets the argument that defines this `DefinitionByReferenceNode`, if any.
   * This predicate should be used instead of `asExpr` when referring to the
   * value of a reference argument _after_ the call has returned. For example,
   * in `f(&x)`, this predicate will have `&x` as its result for the `Node`
   * that represents the new value of `x`.
   */
  Expr asDefiningArgument() { result = this.asDefiningArgument(_) }

  Expr asDefiningArgument(int ind) {
    this.(DefinitionByReferenceNode).getIndex() = ind and
    result = this.(DefinitionByReferenceNode).getArgument()
  }

  Expr asIndirectArgument(int ind) {
    this.(SideEffectOperandNode).getIndex() = ind and
    result = this.(SideEffectOperandNode).getArgument()
  }

  Expr asIndirectArgument() { result = this.asIndirectArgument(_) }

  /** Gets the positional parameter corresponding to this node, if any. */
  Parameter asParameter() { result = this.(ExplicitParameterNode).getParameter() }

  /**
   * Gets the variable corresponding to this node, if any. This can be used for
   * modeling flow in and out of global variables.
   */
  Variable asVariable() { result = this.(VariableNode).getVariable() }

  /**
   * Gets the expression that is partially defined by this node, if any.
   *
   * Partial definitions are created for field stores (`x.y = taint();` is a partial
   * definition of `x`), and for calls that may change the value of an object (so
   * `x.set(taint())` is a partial definition of `x`, and `transfer(&x, taint())` is
   * a partial definition of `&x`).
   */
  Expr asPartialDefinition() { result = this.(PartialDefinitionNode).getDefinedExpr() }

  /**
   * Gets an upper bound on the type of this node.
   */
  IRType getTypeBound() { result = this.getType() }

  /** Gets the location of this element. */
  Location getLocation() { none() } // overridden by subclasses

  /**
   * Holds if this element is at the specified location.
   * The location spans column `startcolumn` of line `startline` to
   * column `endcolumn` of line `endline` in file `filepath`.
   * For more information, see
   * [Locations](https://codeql.github.com/docs/writing-codeql-queries/providing-locations-in-codeql-queries/).
   */
  predicate hasLocationInfo(
    string filepath, int startline, int startcolumn, int endline, int endcolumn
  ) {
    this.getLocation().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
  }

  /** Gets a textual representation of this element. */
  string toString() { none() } // overridden by subclasses
}

/**
 * An instruction, viewed as a node in a data flow graph.
 */
class InstructionNode extends Node, TInstructionNode {
  Instruction instr;

  InstructionNode() { this = TInstructionNode(instr) }

  /** Gets the instruction corresponding to this node. */
  Instruction getInstruction() { result = instr }

  override Declaration getEnclosingCallable() { result = this.getFunction() }

  override Function getFunction() { result = instr.getEnclosingFunction() }

  override IRType getType() { result = instr.getResultIRType() }

  override Location getLocation() { result = instr.getLocation() }

  override string toString() {
    // This predicate is overridden in subclasses. This default implementation
    // does not use `Instruction.toString` because that's expensive to compute.
    result = this.getInstruction().getOpcode().toString()
  }
}

/**
 * An operand, viewed as a node in a data flow graph.
 */
class OperandNode extends Node, TOperandNode {
  Operand op;

  OperandNode() { this = TOperandNode(op) }

  /** Gets the operand corresponding to this node. */
  Operand getOperand() { result = op }

  override Declaration getEnclosingCallable() { result = this.getFunction() }

  override Function getFunction() { result = op.getUse().getEnclosingFunction() }

  override IRType getType() { result = op.getIRType() }

  override Location getLocation() { result = op.getLocation() }

  override string toString() { result = this.getOperand().toString() }
}

class PostFieldUpdateNode extends TPostFieldUpdateNode, PartialDefinitionNode {
  Ssa::Def def;
  FieldAddress fieldAddress;

  PostFieldUpdateNode() { this = TPostFieldUpdateNode(def, fieldAddress) }

  /** Gets the underlying instruction. */
  Ssa::Def getDef() { result = def }

  override Function getFunction() { result = this.getDef().getAddress().getEnclosingFunction() }

  override Declaration getEnclosingCallable() { result = this.getFunction() }

  override IRType getType() { result = this.getDef().getAddress().getResultIRType() }

  override Location getLocation() { result = this.getFieldAddress().getLocation() }

  override string toString() { result = this.getUpdatedField() + " [post update]" }

  FieldAddress getFieldAddress() { result = fieldAddress }

  Field getUpdatedField() { result = fieldAddress.getField() }

  override IndirectOperand getPreUpdateNode() {
    exists(Operand operand |
      hasOperandAndIndex(result, operand, def.getIndex() + 1) and
      conversionFlowStepExcludeFields*(pragma[only_bind_into](operand),
        pragma[only_bind_into](fieldAddress.getObjectAddressOperand()))
    )
  }

  override Expr getDefinedExpr() { result = def.getAddress().getUnconvertedResultExpression() }
}

/**
 * INTERNAL: do not use.
 *
 * A phi node produced by the shared SSA library, viewed as a node in a data flow graph.
 */
class SsaPhiNode extends Node, TSsaPhiNode {
  Ssa::PhiNode phi;

  SsaPhiNode() { this = TSsaPhiNode(phi) }

  /** Gets the phi node associated with this node. */
  Ssa::PhiNode getPhiNode() { result = phi }

  override Declaration getEnclosingCallable() { result = this.getFunction() }

  override Function getFunction() { result = phi.getBasicBlock().getEnclosingFunction() }

  override IRType getType() { result instanceof IRVoidType }

  override Location getLocation() { result = phi.getBasicBlock().getLocation() }

  /** Holds if this phi node has input from the `rnk`'th write operation in block `block`. */
  final predicate hasInputAtRankInBlock(IRBlock block, int rnk) {
    this.hasInputAtRankInBlock(block, rnk, _)
  }

  /**
   * Holds if this phi node has input from the definition `input` (which is the `rnk`'th write
   * operation in block `block`).
   */
  final predicate hasInputAtRankInBlock(IRBlock block, int rnk, Ssa::Definition input) {
    Ssa::phiHasInputFromBlock(phi, input, _) and
    input.definesAt(_, block, rnk)
  }

  override string toString() { result = "Phi" }
}

class SideEffectOperandNode extends Node, IndirectOperand {
  CallInstruction call;
  int argumentIndex;

  SideEffectOperandNode() { operand = call.getArgumentOperand(argumentIndex) }

  CallInstruction getCallInstruction() { result = call }

  Operand getAddressOperand() { result = operand }

  int getArgumentIndex() { result = argumentIndex }

  override Declaration getEnclosingCallable() { result = this.getFunction() }

  override Function getFunction() { result = call.getEnclosingFunction() }

  override IRType getType() { result instanceof IRVoidType }

  override Location getLocation() { result = call.getArgumentOperand(argumentIndex).getLocation() }

  Expr getArgument() { result = call.getArgument(argumentIndex).getUnconvertedResultExpression() }
}

class IndirectParameterNode extends Node, IndirectInstruction {
  InitializeParameterInstruction init;

  IndirectParameterNode() { this.getInstruction() = init }

  InitializeParameterInstruction getInitializeParameterInstruction() { result = init }

  override Declaration getEnclosingCallable() { result = this.getFunction() }

  override Function getFunction() { result = this.getInstruction().getEnclosingFunction() }

  override IRType getType() { result instanceof IRVoidType }

  override Location getLocation() { result = this.getInstruction().getLocation() }
}

class IndirectReturnNode extends IndirectOperand {
  IndirectReturnNode() {
    this.getOperand() = any(ReturnIndirectionInstruction ret).getSourceAddressOperand()
    or
    this.getOperand() = any(ReturnValueInstruction ret).getReturnAddressOperand()
  }

  Operand getAddressOperand() { result = operand }

  override Declaration getEnclosingCallable() { result = this.getFunction() }

  override IRType getType() { result instanceof IRVoidType }
}

class IndirectArgumentOutNode extends Node, TIndirectArgumentOutNode, PostUpdateNode {
  Ssa::CallDef def;
  CallInstruction call;

  IndirectArgumentOutNode() {
    this = TIndirectArgumentOutNode(def) and def.getDefiningInstruction() = call
  }

  int getIndex() { result = def.getIndex() }

  int getArgumentIndex() { call.getArgumentOperand(result) = def.getAddressOperand() }

  CallInstruction getCallInstruction() { result = call }

  Instruction getPrimaryInstruction() { result = call }

  override Declaration getEnclosingCallable() { result = this.getFunction() }

  override Function getFunction() { result = call.getEnclosingFunction() }

  Ssa::CallDef getDef() { result = def }

  override IRType getType() { result instanceof IRVoidType }

  override Location getLocation() { result = def.getLocation() }

  int getIndirection() { result = def.getIndirection() }

  override IndirectOperand getPreUpdateNode() {
    exists(Operand operand |
      hasOperandAndIndex(result, operand, def.getIndex() + 1) and
      conversionFlowStepExcludeFields*(pragma[only_bind_into](operand),
        pragma[only_bind_into](def.getAddressOperand()))
    )
  }

  override string toString() {
    // This string should be unique enough to be helpful but common enough to
    // avoid storing too many different strings.
    result = this.getCallInstruction().getStaticCallTarget().getName() + " output argument"
    or
    not exists(this.getCallInstruction().getStaticCallTarget()) and
    result = "output argument"
  }
}

class IndirectReturnOutNode extends Node, IndirectOperand {
  CallInstruction call;

  IndirectReturnOutNode() { call = this.getOperand().getDef() }

  CallInstruction getCallInstruction() { result = call }
}

class IndirectOperand extends Node, TIndirectOperand {
  Operand operand;
  int ind;

  IndirectOperand() { this = TIndirectOperand(operand, ind) }

  /** Gets the underlying instruction. */
  Operand getOperand() { result = operand }

  int getIndex() { result = ind }

  override Function getFunction() { result = this.getOperand().getDef().getEnclosingFunction() }

  override Declaration getEnclosingCallable() { result = this.getFunction() }

  override IRType getType() { result = this.getOperand().getIRType() }

  override Location getLocation() { result = this.getOperand().getLocation() }

  override string toString() {
    result =
      ToStringUtils::stars().prefix(ind) + instructionNode(this.getOperand().getDef()).toString()
  }
}

class IndirectInstruction extends Node, TIndirectInstruction {
  Instruction instr;
  int ind;

  IndirectInstruction() { this = TIndirectInstruction(instr, ind) }

  /** Gets the underlying instruction. */
  Instruction getInstruction() { result = instr }

  int getIndex() { result = ind }

  override Function getFunction() { result = this.getInstruction().getEnclosingFunction() }

  override Declaration getEnclosingCallable() { result = this.getFunction() }

  override IRType getType() { result = this.getInstruction().getResultIRType() }

  override Location getLocation() { result = this.getInstruction().getLocation() }

  override string toString() {
    result = ToStringUtils::stars().prefix(ind) + instructionNode(this.getInstruction()).toString()
  }
}

/**
 * An expression, viewed as a node in a data flow graph.
 */
class ExprNode extends InstructionNode {
  ExprNode() { exists(instr.getConvertedResultExpression()) }

  /**
   * Gets the non-conversion expression corresponding to this node, if any. If
   * this node strictly (in the sense of `getConvertedExpr`) corresponds to a
   * `Conversion`, then the result is that `Conversion`'s non-`Conversion` base
   * expression.
   */
  Expr getExpr() { result = instr.getUnconvertedResultExpression() }

  /**
   * Gets the expression corresponding to this node, if any. The returned
   * expression may be a `Conversion`.
   */
  Expr getConvertedExpr() { result = instr.getConvertedResultExpression() }

  override string toString() { result = this.asConvertedExpr().toString() }
}

/**
 * The value of a parameter at function entry, viewed as a node in a data
 * flow graph. This includes both explicit parameters such as `x` in `f(x)`
 * and implicit parameters such as `this` in `x.f()`.
 *
 * To match a specific kind of parameter, consider using one of the subclasses
 * `ExplicitParameterNode`, `ThisParameterNode`, or
 * `ParameterIndirectionNode`.
 */
class ParameterNode extends Node {
  ParameterNode() {
    // To avoid making this class abstract, we enumerate its values here
    this.asInstruction() instanceof InitializeParameterInstruction
    or
    this instanceof IndirectParameterNode
  }

  /**
   * Holds if this node is the parameter of `f` at the specified position. The
   * implicit `this` parameter is considered to have position `-1`, and
   * pointer-indirection parameters are at further negative positions.
   */
  predicate isParameterOf(Function f, ParameterPosition pos) { none() } // overridden by subclasses
}

/** An explicit positional parameter, not including `this` or `...`. */
private class ExplicitParameterNode extends ParameterNode, InstructionNode {
  override InitializeParameterInstruction instr;

  ExplicitParameterNode() { exists(instr.getParameter()) }

  override predicate isParameterOf(Function f, ParameterPosition pos) {
    f.getParameter(pos.(DirectPosition).getIndex()) = instr.getParameter()
  }

  /** Gets the `Parameter` associated with this node. */
  Parameter getParameter() { result = instr.getParameter() }

  override string toString() { result = instr.getParameter().toString() }
}

/** An implicit `this` parameter. */
class ThisParameterNode extends ParameterNode, InstructionNode {
  override InitializeParameterInstruction instr;

  ThisParameterNode() { instr.getIRVariable() instanceof IRThisVariable }

  override predicate isParameterOf(Function f, ParameterPosition pos) {
    pos.(DirectPosition).getIndex() = -1 and instr.getEnclosingFunction() = f
  }

  override string toString() { result = "this" }
}

/** A synthetic parameter to model the pointed-to object of a pointer parameter. */
class ParameterIndirectionNode extends ParameterNode instanceof IndirectParameterNode {
  override predicate isParameterOf(Function f, ParameterPosition pos) {
    exists(int index |
      super.getInitializeParameterInstruction().getEnclosingFunction() = f and
      super.getInitializeParameterInstruction().hasIndex(index) and
      pos.(IndirectionPosition).getArgumentIndex() = index and
      pos.(IndirectionPosition).getIndex() = super.getIndex()
    )
  }
}

/**
 * A node associated with an object after an operation that might have
 * changed its state.
 *
 * This can be either the argument to a callable after the callable returns
 * (which might have mutated the argument), or the qualifier of a field after
 * an update to the field.
 *
 * Nodes corresponding to AST elements, for example `ExprNode`, usually refer
 * to the value before the update with the exception of `ClassInstanceExpr`,
 * which represents the value after the constructor has run.
 */
abstract class PostUpdateNode extends Node {
  /**
   * Gets the node before the state update.
   */
  abstract Node getPreUpdateNode();

  override string toString() { result = this.getPreUpdateNode() + " [post update]" }
}

/**
 * The base class for nodes that perform "partial definitions".
 *
 * In contrast to a normal "definition", which provides a new value for
 * something, a partial definition is an expression that may affect a
 * value, but does not necessarily replace it entirely. For example:
 * ```
 * x.y = 1; // a partial definition of the object `x`.
 * x.y.z = 1; // a partial definition of the object `x.y` and `x`.
 * x.setY(1); // a partial definition of the object `x`.
 * setY(&x); // a partial definition of the object `x`.
 * ```
 */
abstract private class PartialDefinitionNode extends PostUpdateNode {
  abstract Expr getDefinedExpr();
}

/**
 * A node that represents the value of a variable after a function call that
 * may have changed the variable because it's passed by reference.
 *
 * A typical example would be a call `f(&x)`. Firstly, there will be flow into
 * `x` from previous definitions of `x`. Secondly, there will be a
 * `DefinitionByReferenceNode` to represent the value of `x` after the call has
 * returned. This node will have its `getArgument()` equal to `&x` and its
 * `getVariableAccess()` equal to `x`.
 */
class DefinitionByReferenceNode extends IndirectArgumentOutNode {
  /** Gets the unconverted argument corresponding to this node. */
  Expr getArgument() { result = def.getAddress().getUnconvertedResultExpression() }

  /** Gets the parameter through which this value is assigned. */
  Parameter getParameter() {
    result = call.getStaticCallTarget().getParameter(this.getArgumentIndex())
  }
}

/**
 * A `Node` corresponding to a variable in the program, as opposed to the
 * value of that variable at some particular point. This can be used for
 * modeling flow in and out of global variables.
 */
class VariableNode extends Node, TVariableNode {
  Variable v;

  VariableNode() { this = TVariableNode(v) }

  /** Gets the variable corresponding to this node. */
  Variable getVariable() { result = v }

  override Function getFunction() { none() }

  override Declaration getEnclosingCallable() {
    // When flow crosses from one _enclosing callable_ to another, the
    // interprocedural data-flow library discards call contexts and inserts a
    // node in the big-step relation used for human-readable path explanations.
    // Therefore we want a distinct enclosing callable for each `VariableNode`,
    // and that can be the `Variable` itself.
    result = v
  }

  override IRType getType() { result.getCanonicalLanguageType().hasUnspecifiedType(v.getType(), _) }

  override Location getLocation() { result = v.getLocation() }

  override string toString() { result = v.toString() }
}

/**
 * Gets the node corresponding to `instr`.
 */
InstructionNode instructionNode(Instruction instr) { result.getInstruction() = instr }

/**
 * Gets the node corresponding to `operand`.
 */
OperandNode operandNode(Operand operand) { result.getOperand() = operand }

/**
 * Gets the `Node` corresponding to the value of evaluating `e` or any of its
 * conversions. There is no result if `e` is a `Conversion`. For data flowing
 * _out of_ an expression, like when an argument is passed by reference, use
 * `definitionByReferenceNodeFromArgument` instead.
 */
ExprNode exprNode(Expr e) { result.getExpr() = e }

/**
 * Gets the `Node` corresponding to the value of evaluating `e`. Here, `e` may
 * be a `Conversion`. For data flowing _out of_ an expression, like when an
 * argument is passed by reference, use
 * `definitionByReferenceNodeFromArgument` instead.
 */
ExprNode convertedExprNode(Expr e) { result.getConvertedExpr() = e }

/**
 * Gets the `Node` corresponding to the value of `p` at function entry.
 */
ExplicitParameterNode parameterNode(Parameter p) { result.getParameter() = p }

/**
 * Gets the `Node` corresponding to a definition by reference of the variable
 * that is passed as unconverted `argument` of a call.
 */
DefinitionByReferenceNode definitionByReferenceNodeFromArgument(Expr argument) {
  result.getArgument() = argument
}

/** Gets the `VariableNode` corresponding to the variable `v`. */
VariableNode variableNode(Variable v) { result.getVariable() = v }

/**
 * DEPRECATED: See UninitializedNode.
 *
 * Gets the `Node` corresponding to the value of an uninitialized local
 * variable `v`.
 */
Node uninitializedNode(LocalVariable v) { none() }

/**
 * Holds if data flows from `nodeFrom` to `nodeTo` in exactly one local
 * (intra-procedural) step.
 */
predicate localFlowStep = localFlowStepCached/2;

private predicate indirectionOperandFlow(IndirectOperand nodeFrom, Node nodeTo) {
  exists(int ind, LoadInstruction load |
    hasOperandAndIndex(nodeFrom, load.getSourceAddressOperand(), ind)
  |
    ind > 1 and
    hasInstructionAndIndex(nodeTo, load, ind - 1)
    or
    ind = 1 and
    nodeTo.asInstruction() = load
  )
  or
  exists(Operand operand, Instruction instr, int index |
    simpleInstructionLocalFlowStep(operand, instr) and
    hasOperandAndIndex(nodeFrom, operand, index) and
    hasInstructionAndIndex(nodeTo, instr, index)
  )
  or
  exists(PointerArithmeticInstruction pointerArith, int index |
    hasOperandAndIndex(nodeFrom, pointerArith.getAnOperand(), index) and
    hasInstructionAndIndex(nodeTo, pointerArith, index)
  )
}

pragma[noinline]
predicate hasOperandAndIndex(IndirectOperand indirectOperand, Operand operand, int index) {
  indirectOperand.getOperand() = operand and
  indirectOperand.getIndex() = index
}

pragma[noinline]
predicate hasInstructionAndIndex(IndirectInstruction indirectInstr, Instruction instr, int index) {
  indirectInstr.getInstruction() = instr and
  indirectInstr.getIndex() = index
}

private predicate indirectionInstructionFlow(IndirectInstruction nodeFrom, IndirectOperand nodeTo) {
  exists(Operand operand, Instruction instr, int index |
    simpleOperandLocalFlowStep(pragma[only_bind_into](instr), pragma[only_bind_into](operand))
  |
    hasOperandAndIndex(nodeTo, operand, index) and
    hasInstructionAndIndex(nodeFrom, instr, index)
  )
}

/**
 * INTERNAL: do not use.
 *
 * This is the local flow predicate that's used as a building block in global
 * data flow. It may have less flow than the `localFlowStep` predicate.
 */
predicate simpleLocalFlowStep(Node nodeFrom, Node nodeTo) {
  // Post update node -> Node flow
  Ssa::postNodeDefUseFlow(nodeFrom, nodeTo)
  or
  // Def-use flow
  Ssa::defUseFlow(nodeFrom, nodeTo)
  or
  // Operand -> Instruction flow
  simpleInstructionLocalFlowStep(nodeFrom.asOperand(), nodeTo.asInstruction())
  or
  // Instruction -> Operand flow
  simpleOperandLocalFlowStep(nodeFrom.asInstruction(), nodeTo.asOperand())
  or
  // Phi node -> Node flow
  Ssa::fromPhiNode(nodeFrom, nodeTo)
  or
  // Node -> Phi node flow
  Ssa::toPhiNode(nodeFrom, nodeTo)
  or
  // Indirect operand -> (indirect) instruction flow
  indirectionOperandFlow(nodeFrom, nodeTo)
  or
  // Indirect instruction -> indirect operand flow
  indirectionInstructionFlow(nodeFrom, nodeTo)
  or
  // Flow through modeled functions
  modelFlow(nodeFrom, nodeTo)
  or
  exists(Ssa::Def def |
    Ssa::nodeToDefOrUse(nodeFrom, def) and
    conversionFlowStepExcludeFields*(nodeTo.(IndirectReturnOutNode).getCallInstruction().getAUse(),
      def.getAddressOperand())
  )
}

pragma[noinline]
private predicate getAddressType(LoadInstruction load, Type t) {
  exists(Instruction address |
    address = load.getSourceAddress() and
    t = address.getResultType()
  )
}

/**
 * Like the AST dataflow library, we want to conflate the address and value of a reference. This class
 * represents the `LoadInstruction` that is generated from a reference dereference.
 */
private class ReferenceDereferenceInstruction extends LoadInstruction {
  ReferenceDereferenceInstruction() {
    exists(ReferenceType ref |
      getAddressType(this, ref) and
      this.getResultType() = ref.getBaseType()
    )
  }
}

private predicate simpleInstructionLocalFlowStep(Operand opFrom, Instruction iTo) {
  iTo.(CopyInstruction).getSourceValueOperand() = opFrom
  or
  iTo.(PhiInstruction).getAnInputOperand() = opFrom
  or
  // Treat all conversions as flow, even conversions between different numeric types.
  iTo.(ConvertInstruction).getUnaryOperand() = opFrom
  or
  iTo.(CheckedConvertOrNullInstruction).getUnaryOperand() = opFrom
  or
  iTo.(InheritanceConversionInstruction).getUnaryOperand() = opFrom
  or
  // Conflate references and values like in AST dataflow.
  iTo.(ReferenceDereferenceInstruction).getSourceAddressOperand() = opFrom
}

private predicate simpleOperandLocalFlowStep(Instruction iFrom, Operand opTo) {
  not opTo instanceof MemoryOperand and
  opTo.getDef() = iFrom
}

private predicate modelFlow(Node nodeFrom, Node nodeTo) {
  exists(
    CallInstruction call, DataFlowFunction func, FunctionInput modelIn, FunctionOutput modelOut
  |
    call.getStaticCallTarget() = func and
    func.hasDataFlow(modelIn, modelOut)
  |
    nodeFrom = callInput(call, modelIn) and
    nodeTo = callOutput(call, modelOut)
    or
    exists(int d |
      nodeFrom = callInput(call, modelIn, d) and
      nodeTo = callOutput(call, modelOut, d)
    )
  )
}

/**
 * Holds if the result is a side effect for instruction `call` on argument
 * index `argument`. This helper predicate makes it easy to join on both of
 * these columns at once, avoiding pathological join orders in case the
 * argument index should get joined first.
 */
pragma[noinline]
SideEffectInstruction getSideEffectFor(CallInstruction call, int argument) {
  call = result.getPrimaryInstruction() and
  argument = result.(IndexedInstruction).getIndex()
}

/**
 * Holds if data flows from `source` to `sink` in zero or more local
 * (intra-procedural) steps.
 */
pragma[inline]
predicate localFlow(Node source, Node sink) { localFlowStep*(source, sink) }

/**
 * Holds if data can flow from `i1` to `i2` in zero or more
 * local (intra-procedural) steps.
 */
pragma[inline]
predicate localInstructionFlow(Instruction e1, Instruction e2) {
  localFlow(instructionNode(e1), instructionNode(e2))
}

/**
 * Holds if data can flow from `e1` to `e2` in zero or more
 * local (intra-procedural) steps.
 */
pragma[inline]
predicate localExprFlow(Expr e1, Expr e2) { localFlow(exprNode(e1), exprNode(e2)) }

private newtype TContent =
  TFieldContent(Field f, int ind) {
    ind = [0 .. Ssa::getMaxIndirectionsForType(f.getUnspecifiedType())] and
    // As reads and writes to union fields can create flow even though the reads and writes
    // target different fields, we don't want a read (write) to create a read (write) step.
    not f.getDeclaringType() instanceof Union
  } or
  TCollectionContent() or // Not used in C/C++
  TArrayContent() // Not used in C/C++.

/**
 * A description of the way data may be stored inside an object. Examples
 * include instance fields, the contents of a collection object, or the contents
 * of an array.
 */
class Content extends TContent {
  /** Gets a textual representation of this element. */
  abstract string toString();

  predicate hasLocationInfo(string path, int sl, int sc, int el, int ec) {
    path = "" and sl = 0 and sc = 0 and el = 0 and ec = 0
  }
}

/** A reference through an instance field. */
class FieldContent extends Content, TFieldContent {
  Field f;
  int ind;

  FieldContent() { this = TFieldContent(f, ind) }

  override string toString() { result = ToStringUtils::stars().prefix(ind) + f.toString() }

  Field getField() { result = f }

  int getIndirection() { result = ind }
}

/** A reference through an array. */
class ArrayContent extends Content, TArrayContent {
  override string toString() { result = "[]" }
}

/** A reference through the contents of some collection-like container. */
private class CollectionContent extends Content, TCollectionContent {
  override string toString() { result = "<element>" }
}

/**
 * A guard that validates some instruction.
 *
 * To use this in a configuration, extend the class and provide a
 * characteristic predicate precisely specifying the guard, and override
 * `checks` to specify what is being validated and in which branch.
 *
 * It is important that all extending classes in scope are disjoint.
 */
class BarrierGuard extends IRGuardCondition {
  /** Override this predicate to hold if this guard validates `instr` upon evaluating to `b`. */
  predicate checksInstr(Instruction instr, boolean b) { none() }

  /** Override this predicate to hold if this guard validates `expr` upon evaluating to `b`. */
  predicate checks(Expr e, boolean b) { none() }

  /** Gets a node guarded by this guard. */
  final Node getAGuardedNode() {
    exists(ValueNumber value, boolean edge |
      (
        this.checksInstr(value.getAnInstruction(), edge)
        or
        this.checks(value.getAnInstruction().getConvertedResultExpression(), edge)
      ) and
      result.asInstruction() = value.getAnInstruction() and
      this.controls(result.asInstruction().getBlock(), edge)
    )
  }
}
