private import cpp
private import DataFlowUtil
private import semmle.code.cpp.ir.IR
private import DataFlowDispatch

/**
 * A data flow node that occurs as the argument of a call and is passed as-is
 * to the callable. Instance arguments (`this` pointer) and read side effects
 * on parameters are also included.
 */
abstract class ArgumentNode extends OperandNode {
  /**
   * Holds if this argument occurs at the given position in the given call.
   * The instance argument is considered to have index `-1`.
   */
  abstract predicate argumentOf(DataFlowCall call, int pos);

  /** Gets the call in which this node is an argument. */
  DataFlowCall getCall() { this.argumentOf(result, _) }
}

/**
 * A data flow node that occurs as the argument to a call, or an
 * implicit `this` pointer argument.
 */
private class PrimaryArgumentNode extends ArgumentNode {
  override ArgumentOperand op;

  PrimaryArgumentNode() { exists(CallInstruction call | op = call.getAnArgumentOperand()) }

  override predicate argumentOf(DataFlowCall call, int pos) { op = call.getArgumentOperand(pos) }

  override string toString() {
    exists(Expr unconverted |
      unconverted = op.getDef().getUnconvertedResultExpression() and
      result = unconverted.toString()
    )
    or
    // Certain instructions don't map to an unconverted result expression. For these cases
    // we fall back to a simpler naming scheme. This can happen in IR-generated constructors.
    not exists(op.getDef().getUnconvertedResultExpression()) and
    (
      result = "Argument " + op.(PositionalArgumentOperand).getIndex()
      or
      op instanceof ThisArgumentOperand and result = "Argument this"
    )
  }
}

/**
 * A data flow node representing the read side effect of a call on a
 * specific parameter.
 */
private class SideEffectArgumentNode extends ArgumentNode {
  override SideEffectOperand op;
  ReadSideEffectInstruction read;

  SideEffectArgumentNode() { op = read.getSideEffectOperand() }

  override predicate argumentOf(DataFlowCall call, int pos) {
    read.getPrimaryInstruction() = call and
    pos = getArgumentPosOfSideEffect(read.getIndex())
  }

  override string toString() {
    result = read.getArgumentDef().getUnconvertedResultExpression().toString() + " indirection"
    or
    // Some instructions don't map to an unconverted result expression. For these cases
    // we fall back to a simpler naming scheme. This can happen in IR-generated constructors.
    not exists(read.getArgumentDef().getUnconvertedResultExpression()) and
    (
      if read.getIndex() = -1
      then result = "Argument this indirection"
      else result = "Argument " + read.getIndex() + " indirection"
    )
  }
}

private newtype TReturnKind =
  TNormalReturnKind() or
  TIndirectReturnKind(ParameterIndex index)

/**
 * A return kind. A return kind describes how a value can be returned
 * from a callable. For C++, this is simply a function return.
 */
class ReturnKind extends TReturnKind {
  /** Gets a textual representation of this return kind. */
  abstract string toString();
}

private class NormalReturnKind extends ReturnKind, TNormalReturnKind {
  override string toString() { result = "return" }
}

private class IndirectReturnKind extends ReturnKind, TIndirectReturnKind {
  ParameterIndex index;

  IndirectReturnKind() { this = TIndirectReturnKind(index) }

  override string toString() { result = "outparam[" + index.toString() + "]" }
}

/** A data flow node that occurs as the result of a `ReturnStmt`. */
class ReturnNode extends InstructionNode {
  Instruction primary;

  ReturnNode() {
    exists(ReturnValueInstruction ret | instr = ret.getReturnValue() and primary = ret)
    or
    exists(ReturnIndirectionInstruction rii |
      instr = rii.getSideEffectOperand().getAnyDef() and primary = rii
    )
  }

  /** Gets the kind of this returned value. */
  abstract ReturnKind getKind();
}

class ReturnValueNode extends ReturnNode {
  override ReturnValueInstruction primary;

  override ReturnKind getKind() { result = TNormalReturnKind() }
}

class ReturnIndirectionNode extends ReturnNode {
  override ReturnIndirectionInstruction primary;

  override ReturnKind getKind() {
    exists(int index |
      primary.hasIndex(index) and
      result = TIndirectReturnKind(index)
    )
  }
}

/** A data flow node that represents the output of a call. */
class OutNode extends InstructionNode {
  OutNode() {
    instr instanceof CallInstruction or
    instr instanceof WriteSideEffectInstruction
  }

  /** Gets the underlying call. */
  abstract DataFlowCall getCall();

  abstract ReturnKind getReturnKind();
}

private class CallOutNode extends OutNode {
  override CallInstruction instr;

  override DataFlowCall getCall() { result = instr }

  override ReturnKind getReturnKind() { result instanceof NormalReturnKind }
}

private class SideEffectOutNode extends OutNode {
  override WriteSideEffectInstruction instr;

  override DataFlowCall getCall() { result = instr.getPrimaryInstruction() }

  override ReturnKind getReturnKind() { result = TIndirectReturnKind(instr.getIndex()) }
}

/**
 * Gets a node that can read the value returned from `call` with return kind
 * `kind`.
 */
OutNode getAnOutNode(DataFlowCall call, ReturnKind kind) {
  // There should be only one `OutNode` for a given `(call, kind)` pair. Showing the optimizer that
  // this is true helps it make better decisions downstream, especially in virtual dispatch.
  result =
    unique(OutNode outNode |
      outNode.getCall() = call and
      outNode.getReturnKind() = kind
    )
}

/**
 * Holds if data can flow from `node1` to `node2` in a way that loses the
 * calling context. For example, this would happen with flow through a
 * global or static variable.
 */
predicate jumpStep(Node n1, Node n2) { none() }

/**
 * Gets a field corresponding to the bit range `[startBit..endBit)` of class `c`, if any.
 */
private Field getAField(Class c, int startBit, int endBit) {
  result.getDeclaringType() = c and
  startBit = 8 * result.getByteOffset() and
  endBit = 8 * result.getType().getSize() + startBit
  or
  exists(Field f, Class cInner |
    f = c.getAField() and
    cInner = f.getUnderlyingType() and
    result = getAField(cInner, startBit - 8 * f.getByteOffset(), endBit - 8 * f.getByteOffset())
  )
}

private newtype TContent =
  TFieldContent(Class c, int startBit, int endBit) { exists(getAField(c, startBit, endBit)) } or
  TCollectionContent() or
  TArrayContent()

/**
 * A reference contained in an object. Examples include instance fields, the
 * contents of a collection object, or the contents of an array.
 */
class Content extends TContent {
  /** Gets a textual representation of this element. */
  abstract string toString();

  predicate hasLocationInfo(string path, int sl, int sc, int el, int ec) {
    path = "" and sl = 0 and sc = 0 and el = 0 and ec = 0
  }
}

private class FieldContent extends Content, TFieldContent {
  Class c;
  int startBit;
  int endBit;

  FieldContent() { this = TFieldContent(c, startBit, endBit) }

  // Ensure that there's just 1 result for `toString`.
  override string toString() { result = min(Field f | f = getAField() | f.toString()) }

  predicate hasOffset(Class cl, int start, int end) { cl = c and start = startBit and end = endBit }

  Field getAField() { result = getAField(c, startBit, endBit) }
}

private class CollectionContent extends Content, TCollectionContent {
  override string toString() { result = "collection" }
}

private class ArrayContent extends Content, TArrayContent {
  ArrayContent() { this = TArrayContent() }

  override string toString() { result = "array content" }
}

private predicate fieldStoreStepNoChi(Node node1, FieldContent f, PostUpdateNode node2) {
  exists(StoreInstruction store, Class c |
    store = node2.asInstruction() and
    store.getSourceValueOperand() = node1.asOperand() and
    getWrittenField(store, f.(FieldContent).getAField(), c) and
    f.hasOffset(c, _, _)
  )
}

private FieldAddressInstruction getFieldInstruction(Instruction instr) {
  result = instr or
  result = instr.(CopyValueInstruction).getUnary()
}

pragma[noinline]
private predicate getWrittenField(Instruction instr, Field f, Class c) {
  exists(FieldAddressInstruction fa |
    fa =
      getFieldInstruction([
          instr.(StoreInstruction).getDestinationAddress(),
          instr.(WriteSideEffectInstruction).getDestinationAddress()
        ]) and
    f = fa.getField() and
    c = f.getDeclaringType()
  )
}

private predicate fieldStoreStepChi(Node node1, FieldContent f, PostUpdateNode node2) {
  exists(ChiPartialOperand operand, ChiInstruction chi |
    chi.getPartialOperand() = operand and
    node1.asOperand() = operand and
    node2.asInstruction() = chi and
    exists(Class c |
      c = chi.getResultType() and
      exists(int startBit, int endBit |
        chi.getUpdatedInterval(startBit, endBit) and
        f.hasOffset(c, startBit, endBit)
      )
      or
      getWrittenField(operand.getDef(), f.getAField(), c) and
      f.hasOffset(c, _, _)
    )
  )
}

private predicate arrayStoreStepChi(Node node1, ArrayContent a, Node node2) {
  a = TArrayContent() and
  (
    exists(ChiPartialOperand operand, ChiInstruction chi, StoreInstruction store |
      chi.getPartialOperand() = operand and
      store = operand.getDef() and
      node1.asOperand() = operand and
      // This `ChiInstruction` will always have a non-conflated result because both `ArrayStoreNode`
      // and `PointerStoreNode` require it in their characteristic predicates.
      node2.(PostUpdateNode).asInstruction() = chi and
      (
        // `x[i] = taint()`
        // This matches the characteristic predicate in `ArrayStoreNode`.
        store.getDestinationAddress() instanceof PointerAddInstruction
        or
        // `*p = taint()`
        // This matches the characteristic predicate in `PointerStoreNode`.
        store.getDestinationAddress().(CopyValueInstruction).getUnary() instanceof LoadInstruction
      )
    )
    or
    // A store step from a pointer indirection to the pointer.
    exists(ReadSideEffectInstruction read, CallInstruction call |
      call = read.getPrimaryInstruction() and
      read.getSideEffectOperand().getAnyDef() = node1.asInstruction() and
      call.getArgumentOperand(read.getIndex()) = node2.asOperand()
    )
  )
}

/**
 * Holds if data can flow from `node1` to `node2` via an assignment to `f`.
 * Thus, `node2` references an object with a field `f` that contains the
 * value of `node1`.
 */
predicate storeStep(Node node1, Content f, Node node2) {
  fieldStoreStepNoChi(node1, f, node2) or
  fieldStoreStepChi(node1, f, node2) or
  arrayStoreStepChi(node1, f, node2) or
  fieldStoreStepAfterArraySuppression(node1, f, node2)
}

// This predicate pushes the correct `FieldContent` onto the access path when the
// `suppressArrayRead` predicate has popped off an `ArrayContent`.
private predicate fieldStoreStepAfterArraySuppression(
  Node node1, FieldContent f, PostUpdateNode node2
) {
  exists(WriteSideEffectInstruction write, ChiInstruction chi, Class c |
    not chi.isResultConflated() and
    node1.asInstruction() = chi and
    node2.asInstruction() = chi and
    chi.getPartial() = write and
    getWrittenField(write, f.getAField(), c) and
    f.hasOffset(c, _, _)
  )
}

bindingset[result, i]
private int unbindInt(int i) { i <= result and i >= result }

pragma[noinline]
private predicate getLoadedField(LoadInstruction load, Field f, Class c) {
  exists(FieldAddressInstruction fa |
    fa = load.getSourceAddress() and
    f = fa.getField() and
    c = f.getDeclaringType()
  )
}

/**
 * Holds if data can flow from `node1` to `node2` via a read of `f`.
 * Thus, `node1` references an object with a field `f` whose value ends up in
 * `node2`.
 */
private predicate fieldReadStep(Node node1, FieldContent f, Node node2) {
  exists(LoadOperand operand |
    node2.asOperand() = operand and
    node1.asInstruction() = operand.getAnyDef() and
    exists(Class c |
      c = operand.getAnyDef().getResultType() and
      exists(int startBit, int endBit |
        operand.getUsedInterval(unbindInt(startBit), unbindInt(endBit)) and
        f.hasOffset(c, startBit, endBit)
      )
      or
      getLoadedField(operand.getUse(), f.getAField(), c) and
      f.hasOffset(c, _, _)
    )
  )
}

/**
 * When a store step happens in a function that looks like an array write such as:
 * ```cpp
 * void f(int* pa) {
 *   pa = source();
 * }
 * ```
 * it can be a write to an array, but it can also happen that `f` is called as `f(&a.x)`. If that is
 * the case, the `ArrayContent` that was written by the call to `f` should be popped off the access
 * path, and a `FieldContent` containing `x` should be pushed instead.
 * So this case pops `ArrayContent` off the access path, and the `fieldStoreStepAfterArraySuppression`
 * predicate in `storeStep` ensures that we push the right `FieldContent` onto the access path.
 */
predicate suppressArrayRead(Node node1, ArrayContent a, Node node2) {
  a = TArrayContent() and
  exists(WriteSideEffectInstruction write, ChiInstruction chi |
    node1.asInstruction() = write and
    node2.asInstruction() = chi and
    chi.getPartial() = write and
    getWrittenField(write, _, _)
  )
}

private class ArrayToPointerConvertInstruction extends ConvertInstruction {
  ArrayToPointerConvertInstruction() {
    this.getUnary().getResultType() instanceof ArrayType and
    this.getResultType() instanceof PointerType
  }
}

private Instruction skipOneCopyValueInstructionRec(CopyValueInstruction copy) {
  copy.getUnary() = result and not result instanceof CopyValueInstruction
  or
  result = skipOneCopyValueInstructionRec(copy.getUnary())
}

private Instruction skipCopyValueInstructions(Operand op) {
  not result instanceof CopyValueInstruction and result = op.getDef()
  or
  result = skipOneCopyValueInstructionRec(op.getDef())
}

private predicate arrayReadStep(Node node1, ArrayContent a, Node node2) {
  a = TArrayContent() and
  (
    // Explicit dereferences such as `*p` or `p[i]` where `p` is a pointer or array.
    exists(LoadOperand operand, Instruction address |
      operand.isDefinitionInexact() and
      node1.asInstruction() = operand.getAnyDef() and
      operand = node2.asOperand() and
      address = skipCopyValueInstructions(operand.getAddressOperand()) and
      (
        address instanceof LoadInstruction or
        address instanceof ArrayToPointerConvertInstruction or
        address instanceof PointerOffsetInstruction
      )
    )
    or
    // A read step from a pointer to its indirection.
    exists(ReadSideEffectInstruction read, CallInstruction call |
      call = read.getPrimaryInstruction() and
      node1.asInstruction() = read.getArgumentDef() and
      node2.asOperand() = read.getSideEffectOperand()
    )
  )
}

/**
 * In cases such as:
 * ```cpp
 * void f(int* pa) {
 *   *pa = source();
 * }
 * ...
 * int x;
 * f(&x);
 * use(x);
 * ```
 * the load on `x` in `use(x)` will exactly overlap with its definition (in this case the definition
 * is a `WriteSideEffect`). This predicate pops the `ArrayContent` (pushed by the store in `f`)
 * from the access path.
 */
private predicate exactReadStep(Node node1, ArrayContent a, Node node2) {
  a = TArrayContent() and
  exists(WriteSideEffectInstruction write, ChiInstruction chi |
    not chi.isResultConflated() and
    chi.getPartial() = write and
    node1.asInstruction() = write and
    node2.asInstruction() = chi and
    // To distinquish this case from the `arrayReadStep` case we require that the entire variable was
    // overwritten by the `WriteSideEffectInstruction` (i.e., there is a load that reads the
    // entire variable).
    exists(LoadInstruction load | load.getSourceValue() = chi)
  )
}

/**
 * Holds if data can flow from `node1` to `node2` via a read of `f`.
 * Thus, `node1` references an object with a field `f` whose value ends up in
 * `node2`.
 */
predicate readStep(Node node1, Content f, Node node2) {
  fieldReadStep(node1, f, node2) or
  arrayReadStep(node1, f, node2) or
  exactReadStep(node1, f, node2) or
  suppressArrayRead(node1, f, node2)
}

/**
 * Holds if values stored inside content `c` are cleared at node `n`.
 */
predicate clearsContent(Node n, Content c) {
  none() // stub implementation
}

/** Gets the type of `n` used for type pruning. */
DataFlowType getNodeType(Node n) { result = n.getType() }

/** Gets a string representation of a type returned by `getNodeType`. */
string ppReprType(DataFlowType t) { none() } // stub implementation

Type hasConversionTo(Type type) {
  result.getUnspecifiedType() = type.getUnspecifiedType()
  or
  exists(Conversion convert |
    convert.getExpr().getUnspecifiedType() = type.getUnspecifiedType() and
    result = convert.getUnspecifiedType()
  )
}

/**
 * Holds if `t1` and `t2` are compatible, that is, whether data can flow from
 * a node of type `t1` to a node of type `t2`.
 */
pragma[inline]
predicate compatibleTypes(DataFlowType t1, DataFlowType t2) { t2 = hasConversionTo+(t1) }

private predicate suppressUnusedNode(Node n) { any() }

//////////////////////////////////////////////////////////////////////////////
// Java QL library compatibility wrappers
//////////////////////////////////////////////////////////////////////////////
/** A node that performs a type cast. */
class CastNode extends InstructionNode {
  CastNode() { none() } // stub implementation
}

/**
 * A function that may contain code or a variable that may contain itself. When
 * flow crosses from one _enclosing callable_ to another, the interprocedural
 * data-flow library discards call contexts and inserts a node in the big-step
 * relation used for human-readable path explanations.
 */
class DataFlowCallable = Declaration;

class DataFlowExpr = Expr;

class DataFlowType = Type;

/** A function call relevant for data flow. */
class DataFlowCall extends CallInstruction {
  Function getEnclosingCallable() { result = this.getEnclosingFunction() }
}

predicate isUnreachableInCall(Node n, DataFlowCall call) { none() } // stub implementation

int accessPathLimit() { result = 5 }

/** The unit type. */
private newtype TUnit = TMkUnit()

/** The trivial type with a single element. */
class Unit extends TUnit {
  /** Gets a textual representation of this element. */
  string toString() { result = "unit" }
}

/**
 * Holds if `n` does not require a `PostUpdateNode` as it either cannot be
 * modified or its modification cannot be observed, for example if it is a
 * freshly created object that is not saved in a variable.
 *
 * This predicate is only used for consistency checks.
 */
predicate isImmutableOrUnobservable(Node n) {
  // The rules for whether an IR argument gets a post-update node are too
  // complex to model here.
  any()
}

/** Holds if `n` should be hidden from path explanations. */
predicate nodeIsHidden(Node n) { n instanceof OperandNode and not n instanceof ArgumentNode }
