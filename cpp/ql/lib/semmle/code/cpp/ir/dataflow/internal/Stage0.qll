private import cpp
private import semmle.code.cpp.ir.IR
private import Base
private import Node0ToString
private import StageSig
private import semmle.code.cpp.ir.internal.CppType
private import codeql.dataflow.internal.AccessPathSyntax as AccessPath

cached
private newtype TNode =
  TInstructionNode0(Instruction i) {
    not ignoreInstruction(i) and
    not exists(Operand op | not ignoreOperand(op) and i = getIRRepresentationOfOperand(op)) and
    // We exclude `void`-typed instructions because they cannot contain data.
    // However, if the instruction is a glvalue, and their type is `void`, then the result
    // type of the instruction is really `void*`, and thus we still want to have a dataflow
    // node for it.
    (not i.getResultType() instanceof VoidType or i.isGLValue())
  } or
  TMultipleUseOperandNode0(Operand op) {
    not ignoreOperand(op) and not exists(getIRRepresentationOfOperand(op))
  } or
  TSingleUseOperandNode0(Operand op) {
    not ignoreOperand(op) and exists(getIRRepresentationOfOperand(op))
  }

predicate conversionFlow(Operand opFrom, Instruction instrTo, boolean isPointerArith) {
  isPointerArith = false and
  (
    instrTo.(CopyValueInstruction).getSourceValueOperand() = opFrom
    or
    instrTo.(ConvertInstruction).getUnaryOperand() = opFrom
    or
    instrTo.(CheckedConvertOrNullInstruction).getUnaryOperand() = opFrom
    or
    instrTo.(InheritanceConversionInstruction).getUnaryOperand() = opFrom
    or
    exists(BuiltInInstruction builtIn |
      builtIn = instrTo and
      // __builtin_bit_cast
      builtIn.getBuiltInOperation() instanceof BuiltInBitCast and
      opFrom = builtIn.getAnOperand()
    )
  )
  or
  isPointerArith = true and
  instrTo.(PointerArithmeticInstruction).getLeftOperand() = opFrom
}

private predicate simpleInstructionLocalFlowStep(Operand opFrom, Instruction iTo) {
  // Treat all conversions as flow, even conversions between different numeric types.
  conversionFlow(opFrom, iTo, false)
  or
  iTo.(CopyInstruction).getSourceValueOperand() = opFrom
}

module Stage0 implements StageSig {
  /**
   * A cut-down `DataFlow::Node` class that does not depend on the output of SSA.
   * This can thus be safely used in the SSA computations themselves, as well as
   * in construction of other node classes (`TIRDataFlowNode`).
   */
  class Node extends TNode {
    /**
     * INTERNAL: Do not use.
     */
    Declaration getEnclosingCallable() { none() } // overridden in subclasses

    /** Gets the function to which this node belongs, if any. */
    Declaration getFunction() { none() } // overridden in subclasses

    /**
     * Gets the type of this node.
     *
     * If `isGLValue()` holds, then the type of this node
     * should be thought of as "pointer to `getType()`".
     */
    DataFlowType getType() { none() } // overridden in subclasses

    /** Gets the instruction corresponding to this node, if any. */
    Instruction asInstruction() { result = this.(InstructionNode).getInstruction() }

    /** Gets the operands corresponding to this node, if any. */
    Operand asOperand() { result = this.(OperandNode).getOperand() }

    /** Gets the location of this node. */
    final Location getLocation() { result = this.getLocationImpl() }

    /** INTERNAL: Do not use. */
    Location getLocationImpl() {
      none() // overridden by subclasses
    }

    /** INTERNAL: Do not use. */
    string toStringImpl() {
      none() // overridden by subclasses
    }

    /** Gets a textual representation of this node. */
    final string toString() { result = this.toStringImpl() }

    /** Holds if the value of this node is a glvalue */
    predicate isGLValue() { none() } // overridden in subclasses

    predicate hasIndexInBlock(IRBlock block, int i) {
      block.getInstruction(i) = this.asInstruction()
      or
      block.getInstruction(i) = this.asOperand().getUse()
    }

    string stars() { result = "" }
  }

  /**
   * An instruction, viewed as a node in a data flow graph.
   */
  abstract private class InstructionNodeImpl extends Node {
    Instruction instr;

    /** Gets the instruction corresponding to this node. */
    Instruction getInstruction() { result = instr }

    override Declaration getEnclosingCallable() { result = this.getFunction() }

    override Declaration getFunction() { result = instr.getEnclosingFunction() }

    override DataFlowType getType() { result = getInstructionType(instr, _) }

    override string toStringImpl() { result = instructionToString(instr) }

    override Location getLocationImpl() {
      if exists(instr.getAst().getLocation())
      then result = instr.getAst().getLocation()
      else result instanceof UnknownDefaultLocation
    }

    final override predicate isGLValue() { exists(getInstructionType(instr, true)) }
  }

  final class InstructionNode = InstructionNodeImpl;

  InstructionNode instructionNode(Instruction instr) { result.getInstruction() = instr }

  /**
   * An operand, viewed as a node in a data flow graph.
   */
  abstract private class OperandNodeImpl extends Node {
    Operand op;

    /** Gets the operand corresponding to this node. */
    Operand getOperand() { result = op }

    override Declaration getEnclosingCallable() { result = this.getFunction() }

    override Declaration getFunction() { result = op.getUse().getEnclosingFunction() }

    override DataFlowType getType() { result = getOperandType(op, _) }

    override string toStringImpl() { result = operandToString(op) }

    override Location getLocationImpl() {
      if exists(op.getDef().getAst().getLocation())
      then result = op.getDef().getAst().getLocation()
      else result instanceof UnknownDefaultLocation
    }

    final override predicate isGLValue() { exists(getOperandType(op, true)) }
  }

  final class OperandNode = OperandNodeImpl;

  OperandNode operandNode(Operand operand) { result.getOperand() = operand }

  /**
   * An instruction without an operand that is used only once, viewed as a node in a data flow graph.
   */
  private class InstructionInstructionNode0 extends InstructionNodeImpl, TInstructionNode0 {
    InstructionInstructionNode0() { this = TInstructionNode0(instr) }
  }

  /**
   * An instruction with an operand that is used only once, viewed as a node in a data flow graph.
   */
  private class SingleUseOperandInstructionNode0 extends InstructionNodeImpl, TSingleUseOperandNode0
  {
    SingleUseOperandInstructionNode0() {
      exists(Operand op |
        this = TSingleUseOperandNode0(op) and
        instr = getIRRepresentationOfOperand(op)
      )
    }
  }

  /**
   * An operand that is used multiple times, viewed as a node in a data flow graph.
   */
  private class MultipleUseOperandNode0 extends OperandNodeImpl, TMultipleUseOperandNode0 {
    MultipleUseOperandNode0() { this = TMultipleUseOperandNode0(op) }
  }

  /**
   * An operand that is used only once, viewed as a node in a data flow graph.
   */
  private class SingleUseOperandNode0 extends OperandNodeImpl, TSingleUseOperandNode0 {
    SingleUseOperandNode0() { this = TSingleUseOperandNode0(op) }
  }

  class IndirectInstructionNode extends Node {
    IndirectInstructionNode() { none() }

    predicate hasInstructionAndIndirectionIndex(Instruction operand, int indirectionIndex) {
      none()
    }
  }

  class IndirectOperandNode extends Node {
    IndirectOperandNode() { none() }

    predicate hasOperandAndIndirectionIndex(Operand operand, int indirectionIndex) { none() }
  }

  predicate hasOperandAndIndex(IndirectOperandNode n, Operand op, int indirectionIndex) { none() }

  predicate hasInstructionAndIndex(IndirectInstructionNode n, Instruction op, int indirectionIndex) {
    none()
  }

  predicate nodeHasOperand(Node node, Operand operand, int indirectionIndex) {
    node.asOperand() = operand and indirectionIndex = 0
  }

  predicate nodeHasInstruction(Node node, Instruction instr, int indirectionIndex) {
    node.asInstruction() = instr and indirectionIndex = 0
  }

  private predicate simpleOperandLocalFlowStep(Instruction iFrom, Operand opTo) {
    not opTo instanceof MemoryOperand and
    opTo.getDef() = iFrom
  }

  predicate localFlowStep(Node nodeFrom, Node nodeTo) {
    // Operand -> Instruction flow
    simpleInstructionLocalFlowStep(nodeFrom.asOperand(), nodeTo.asInstruction())
    or
    // Instruction -> Operand flow
    exists(Instruction iFrom, Operand opTo |
      iFrom = nodeFrom.asInstruction() and opTo = nodeTo.asOperand()
    |
      simpleOperandLocalFlowStep(iFrom, opTo) and
      // Omit when the instruction node also represents the operand.
      not iFrom = getIRRepresentationOfOperand(opTo)
    )
  }

  class DataFlowCallable extends Declaration {
    Declaration getUnderlyingCallable() { result = this }
  }

  DataFlowCallable nodeGetEnclosingCallable(Node n) {
    result = n.asInstruction().getEnclosingFunction()
    or
    result = n.asOperand().getUse().getEnclosingFunction()
  }

  class DataFlowCall = CallInstruction;

  private newtype TPosition =
    TDirectPosition(int argumentIndex) { exists(any(CallInstruction c).getArgument(argumentIndex)) }

  class Position extends TPosition {
    string toString() {
      exists(int argumentIndex | argumentIndex = this.getArgumentIndex() |
        if argumentIndex = -1 then result = "this pointer" else result = argumentIndex.toString()
      )
    }

    int getArgumentIndex() { this = TDirectPosition(result) }
  }

  bindingset[s]
  Position decodePosition(string s) { result = TDirectPosition(AccessPath::parseInt(s)) }

  class ArgumentNode instanceof OperandNode {
    CallInstruction call;
    int argumentIndex;

    ArgumentNode() { super.getOperand() = call.getArgumentOperand(argumentIndex) }

    string toString() { result = super.toString() }

    predicate argumentOf(DataFlowCall call_, Position pos) {
      pos.getArgumentIndex() = argumentIndex and
      call = call_
    }
  }

  private newtype TReturnKind = TNormalReturn()

  class ReturnKind extends TReturnKind {
    string toString() { result = "return" }

    int getIndirectionIndex() { result = 0 }
  }

  private Operand fullyConvertedCallStepImpl(Operand op) {
    not exists(getANonConversionUse(op)) and
    exists(Instruction instr |
      conversionFlow(op, instr, _) and // TODO: What about additional conversion flows?
      result = getAUse(instr)
    )
  }

  private Operand fullyConvertedCallStep(Operand op) {
    result = unique( | | fullyConvertedCallStepImpl(op))
  }

  /**
   * Gets a use of `operand` that is:
   * - not ignored for dataflow purposes, and
   * - not a conversion-like instruction.
   */
  private Instruction getANonConversionUse(Operand operand) {
    result = getUse(operand) and
    not conversionFlow(_, result, _) // TODO: What about additional flow conversions?
  }

  /**
   * Gets an operand that represents the use of the value of `call` following
   * a sequence of conversion-like instructions.
   *
   * Note that `operand` is not functionally determined by `call` since there
   * can be multiple sequences of disjoint conversions following a call. For example,
   * consider an example like:
   * ```cpp
   * long f();
   * int y;
   * long x = (long)(y = (int)f());
   * ```
   * in this case, there'll be a long-to-int conversion on `f()` before the value is assigned to `y`,
   * and there will be an int-to-long conversion on `(int)f()` before the value is assigned to `x`.
   */
  private predicate operandForFullyConvertedCallImpl(Operand operand, DataFlowCall call) {
    exists(getANonConversionUse(operand)) and
    (
      operand = getAUse(call)
      or
      operand = fullyConvertedCallStep*(getAUse(call))
    )
  }

  /**
   * Gets the operand that represents the use of the value of `call` following
   * a sequence of conversion-like instructions, if a unique operand exists.
   */
  private predicate operandForFullyConvertedCall(Operand operand, DataFlowCall call) {
    operand = unique(Operand cand | operandForFullyConvertedCallImpl(cand, call))
  }

  private predicate instructionForFullyConvertedCallWithConversions(
    Instruction instr, DataFlowCall call
  ) {
    instr =
      getUse(unique(Operand operand |
          operand = fullyConvertedCallStep*(getAUse(call)) and
          not exists(fullyConvertedCallStep(operand))
        ))
  }

  /**
   * Gets the instruction that represents the first use of the value of `call` following
   * a sequence of conversion-like instructions.
   *
   * This predicate only holds if there is no suitable operand (i.e., no operand of a non-
   * conversion instruction) to use to represent the value of `call` after conversions.
   */
  private predicate instructionForFullyConvertedCall(Instruction instr, DataFlowCall call) {
    // Only pick an instruction for the call if we cannot pick a unique operand.
    not operandForFullyConvertedCall(_, call) and
    (
      // If there is no use of the call then we pick the call instruction
      not instructionForFullyConvertedCallWithConversions(_, call) and
      instr = call
      or
      // Otherwise, flow to the first instruction that defines multiple operands.
      instructionForFullyConvertedCallWithConversions(instr, call)
    )
  }

  /** Holds if `node` represents the output node for `call`. */
  private predicate simpleOutNode(Node node, DataFlowCall call) {
    operandForFullyConvertedCall(node.asOperand(), call)
    or
    instructionForFullyConvertedCall(node.asInstruction(), call)
  }

  class OutNode extends Node {
    DataFlowCall call;

    OutNode() { simpleOutNode(this, call) }

    DataFlowCall getCall() { result = call }

    ReturnKind getReturnKind() { any() }
  }

  class ReturnNode extends Node {
    // We could handle simple return nodes here, but it's easier to just do it in stage 1
    ReturnNode() { none() }

    ReturnKind getKind() { any() }
  }

  class PostUpdateNode extends Node {
    PostUpdateNode() { none() }

    Node getPreUpdateNode() { none() }
  }
}

module Stage0Output {
  private import semmle.code.cpp.models.interfaces.PointerWrapper

  private predicate isIndirectionType(Type t) { t instanceof Indirection }

  private predicate hasUnspecifiedBaseType(Indirection t, Type base) {
    base = t.getBaseType().getUnspecifiedType()
  }

  /**
   * Holds if `t2` is the same type as `t1`, but after stripping away `result` number
   * of indirections.
   * Furthermore, specifies in `t2` been deeply stripped and typedefs has been resolved.
   */
  private int getNumberOfIndirectionsImpl(Type t1, Type t2) =
    shortestDistances(isIndirectionType/1, hasUnspecifiedBaseType/2)(t1, t2, result)

  /**
   * An abstract class for handling indirections.
   *
   * Extend this class to make a type behave as a pointer for the
   * purposes of dataflow.
   */
  abstract class Indirection extends Type {
    Type baseType;

    /** Gets the type of this indirection. */
    final Type getType() { result = this }

    /**
     * Gets the number of indirections supported by this type.
     *
     * For example, the number of indirections of a variable `p` of type
     * `int**` is `3` (i.e., `p`, `*p` and `**p`).
     */
    final int getNumberOfIndirections() {
      result =
        getNumberOfIndirectionsImpl(this.getType(), any(Type end | not end instanceof Indirection))
    }

    /**
     * Holds if `deref` is an instruction that behaves as a `LoadInstruction`
     * that loads the value computed by `address`.
     */
    predicate isAdditionalDereference(Instruction deref, Operand address) { none() }

    /**
     * Holds if `value` is written to the address computed by `address`.
     *
     * `certain` is `true` if this write is guaranteed to write to the address.
     */
    predicate isAdditionalWrite(Stage0::Node value, Operand address, boolean certain) { none() }

    /**
     * Gets the base type of this indirection, after specifiers have been deeply
     * stripped and typedefs have been resolved.
     *
     * For example, the base type of `int*&` is `int*`, and the base type of `int*` is `int`.
     */
    final Type getBaseType() { result = baseType }

    /**
     * Holds if the step from `opFrom` to `instrTo` should be considered a conversion
     * from `opFrom` to `instrTo`.
     */
    predicate isAdditionalConversionFlow(Operand opFrom, Instruction instrTo) { none() }
  }

  private class PointerOrArrayOrReferenceTypeIndirection extends Stage0Output::Indirection instanceof PointerOrArrayOrReferenceType
  {
    PointerOrArrayOrReferenceTypeIndirection() {
      baseType = PointerOrArrayOrReferenceType.super.getBaseType()
    }
  }

  private class PointerWrapperTypeIndirection extends Stage0Output::Indirection instanceof PointerWrapper
  {
    PointerWrapperTypeIndirection() { baseType = PointerWrapper.super.getBaseType() }

    override predicate isAdditionalDereference(Instruction deref, Operand address) {
      exists(CallInstruction call, Stage0::OutNode out |
        out.getCall() = call and
        out.asOperand() = getAUse(deref) and
        this = call.getStaticCallTarget().getClassAndName(["operator*", "operator->", "get"]) and
        address = call.getThisArgumentOperand()
      )
    }
  }

  private module IteratorIndirections {
    import semmle.code.cpp.models.interfaces.Iterator as Interfaces
    import semmle.code.cpp.models.implementations.Iterator as Iterator
    import semmle.code.cpp.models.implementations.StdContainer as StdContainer

    class IteratorIndirection extends Stage0Output::Indirection instanceof Interfaces::Iterator {
      IteratorIndirection() {
        not this instanceof PointerOrArrayOrReferenceTypeIndirection and
        baseType = super.getValueType()
      }

      override predicate isAdditionalWrite(Stage0::Node value, Operand address, boolean certain) {
        exists(CallInstruction call | call.getArgumentOperand(0) = value.asOperand() |
          this = call.getStaticCallTarget().getClassAndName("operator=") and
          address = call.getThisArgumentOperand() and
          certain = false
        )
      }

      override predicate isAdditionalConversionFlow(Operand opFrom, Instruction instrTo) {
        // This is a bit annoying: Consider the following snippet:
        // ```
        // struct MyIterator {
        //       ...
        //       insert_iterator_by_trait operator*();
        //       insert_iterator_by_trait operator=(int x);
        //   };
        // ...
        // MyIterator it;
        // ...
        // *it = source();
        // ```
        // The qualifier to `operator*` will undergo prvalue-to-xvalue conversion and a
        // temporary object will be created. Thus, the IR for the call to `operator=` will
        // look like (simplified):
        // ```
        // r1(glval<MyIterator>) = VariableAddress[it]        :
        // r2(glval<unknown>)    = FunctionAddress[operator*] :
        // r3(MyIterator)        = Call[operator*]            : func:r2, this:r1
        // r4(glval<MyIterator>) = VariableAddress[#temp]     :
        // m1(MyIterator)        = Store[#temp]               : &:r4, r3
        // r5(glval<unknown>)    = FunctionAddress[operator=] :
        // r6(glval<unknown>)    = FunctionAddress[source]    :
        // r7(int)               = Call[source]               : func:r6
        // r8(MyIterator)        = Call[operator=]            : func:r5, this:r4, 0:r7
        // ```
        // in order to properly recognize that the qualifier to the call to `operator=` accesses
        // `it` we look for the store that writes to the temporary object, and use the source value
        // of that store as the "address" to continue searching for the base variable `it`.
        exists(StoreInstruction store, VariableInstruction var |
          var = instrTo and
          var.getIRVariable() instanceof IRTempVariable and
          opFrom.getType() = this and
          store.getSourceValueOperand() = opFrom and
          store.getDestinationAddress() = var
        )
        or
        // A call to `operator++` or `operator--` is the iterator equivalent version of a
        // pointer arithmetic instruction.
        exists(CallInstruction call |
          instrTo = call and
          call.getStaticCallTarget() instanceof Iterator::IteratorCrementMemberOperator and
          opFrom = call.getThisArgumentOperand()
        )
      }
    }
  }

  /**
   * Returns `t`, but stripped of the outermost pointer, reference, etc.
   *
   * For example, `stripPointers(int*&)` is `int*` and `stripPointers(int*)` is
   * `int`.
   */
  private Type stripPointer(Type t) {
    result = any(Indirection ind | ind.getType() = t).getBaseType()
    or
    result = t.(PointerToMemberType).getBaseType()
    or
    result = t.(FunctionPointerIshType).getBaseType()
  }

  /**
   * Returns `t`, but stripped of the outer-most `indirectionIndex` number of
   * indirections.
   */
  private Type getTypeImpl0(Type t, int indirectionIndex) {
    indirectionIndex = 0 and
    result = t
    or
    indirectionIndex > 0 and
    exists(Type stripped |
      stripped = stripPointer(t.stripTopLevelSpecifiers()) and
      // We need to avoid the case where `stripPointer(t) = t` (which can happen
      // on iterators that specify a `value_type` that is the iterator itself).
      // Such a type would create an infinite loop otherwise. For these cases we
      // simply don't produce a result for `getTypeImpl`.
      // To be on the safe side, we check whether the _unspecified_ type has
      // changed since this also prevents an infinite loop when `stripped` and
      // `t` only differ by const'ness or volatile'ness.
      stripped.getUnspecifiedType() != t.getUnspecifiedType() and
      result = getTypeImpl0(stripped, indirectionIndex - 1)
    )
  }

  /**
   * INTERNAL: Do not use.
   *
   * Returns `t`, but stripped of the outer-most `indirectionIndex` number of
   * indirections.
   *
   * If `indirectionIndex` cannot be stripped off `t`, an `UnknownType` is
   * returned.
   */
  bindingset[t, indirectionIndex]
  pragma[inline_late]
  Type getTypeImpl(Type t, int indirectionIndex) {
    result = getTypeImpl0(t, indirectionIndex)
    or
    // If we cannot produce the right type we return an error type.
    // This can sometimes happen when we don't know the real
    // type of a void pointer.
    not exists(getTypeImpl0(t, indirectionIndex)) and
    result instanceof UnknownType
  }

  /**
   * Gets the maximum number of indirections a glvalue of type `type` can have.
   * For example:
   * - If `type = int`, the result is 1
   * - If `type = MyStruct`, the result is 1
   * - If `type = char*`, the result is 2
   */
  int getMaxIndirectionsForType(Type type) {
    result = countIndirectionsForCppType(getTypeForGLValue(type))
  }

  /**
   * Gets the maximum number of indirections a value of type `type` can have.
   *
   * Note that this predicate is intended to be called on unspecified types
   * (i.e., `countIndirections(e.getUnspecifiedType())`).
   */
  private int countIndirections(Type t) {
    // We special case void pointers because we don't know how many indirections
    // they really have. In a Glorious Future we could do a pre-analysis to figure out
    // which kinds of values flows into the type and use the maximum number of
    // indirections flowinginto the type.
    if t instanceof VoidPointerType
    then result = 2
    else (
      result = any(Indirection ind | ind.getType() = t).getNumberOfIndirections()
      or
      // If there is an indirection for the type, but we cannot count the number of indirections
      // it means we couldn't reach a non-indirection type by stripping off indirections. This
      // can occur if an iterator specifies itself as the value type. In this case we default to
      // 1 indirection fore the type.
      exists(Indirection ind |
        ind.getType() = t and
        not exists(ind.getNumberOfIndirections()) and
        result = 1
      )
      or
      not exists(Indirection ind | ind.getType() = t) and
      result = 0
    )
  }

  /**
   * Gets the maximum number of indirections a value of C++
   * type `langType` can have.
   */
  int countIndirectionsForCppType(CppType langType) {
    exists(Type type | langType.hasType(type, true) |
      result = 1 + countIndirections(type.getUnspecifiedType())
    )
    or
    exists(Type type | langType.hasType(type, false) |
      result = countIndirections(type.getUnspecifiedType())
    )
  }

  /**
   * Holds if `deref` is the result of loading the value at the address
   * represented by `address`.
   *
   * If `additional = true` then the dereference comes from an `Indirection`
   * class (such as a call to an iterator's `operator*`), and if
   * `additional = false` the dereference is a `LoadInstruction`.
   */
  predicate isDereference(Instruction deref, Operand address, boolean additional) {
    any(Indirection ind).isAdditionalDereference(deref, address) and
    additional = true
    or
    deref.(LoadInstruction).getSourceAddressOperand() = address and
    additional = false
  }

  /**
   * Holds if the underlying IR has a suitable operand to represent a value
   * that would otherwise need to be represented by a dedicated `RawIndirectOperand` value.
   *
   * Such operands do not create new `RawIndirectOperand` values, but are
   * instead associated with the operand returned by this predicate.
   */
  predicate hasIRRepresentationOfIndirectOperand(
    Operand operand, int indirectionIndex, Operand operandRepr, int indirectionIndexRepr
  ) {
    indirectionIndex = [1 .. countIndirectionsForCppType(getLanguageType(operand))] and
    exists(Instruction load |
      isDereference(load, operand, false) and
      operandRepr = unique( | | getAUse(load)) and
      indirectionIndexRepr = indirectionIndex - 1
    )
  }

  /**
   * Holds if the underlying IR has a suitable instruction to represent a value
   * that would otherwise need to be represented by a dedicated `RawIndirectInstruction` value.
   *
   * Such instructions do not create new `RawIndirectOperand` values, but are
   * instead associated with the instruction returned by this predicate.
   */
  predicate hasIRRepresentationOfIndirectInstruction(
    Instruction instr, int indirectionIndex, Instruction instrRepr, int indirectionIndexRepr
  ) {
    indirectionIndex = [1 .. countIndirectionsForCppType(getResultLanguageType(instr))] and
    exists(Instruction load, Operand address |
      address = unique( | | getAUse(instr)) and
      isDereference(load, address, false) and
      instrRepr = load and
      indirectionIndexRepr = indirectionIndex - 1
    )
  }

  /**
   * Holds if `indirectionIndex` is a valid non-zero indirection index for
   * operand `op`. That is, `indirectionIndex` is between 1 and the maximum
   * indirection for the operand's type.
   */
  predicate hasIndirectOperand(Operand op, int indirectionIndex) {
    exists(CppType type, int m |
      not ignoreOperand(op) and
      type = getLanguageType(op) and
      m = countIndirectionsForCppType(type) and
      indirectionIndex = [1 .. m]
    )
  }

  /**
   * Holds if the `(operand, indirectionIndex)` columns should be
   * assigned a `RawIndirectOperand` value.
   */
  predicate hasRawIndirectOperand(Operand op, int indirectionIndex) {
    hasIndirectOperand(op, indirectionIndex) and
    not hasIRRepresentationOfIndirectOperand(op, indirectionIndex, _, _)
  }

  /**
   * Holds if the `(instr, indirectionIndex)` columns should be
   * assigned a `RawIndirectInstruction` value.
   */
  predicate hasRawIndirectInstruction(Instruction instr, int indirectionIndex) {
    exists(CppType type, int m |
      not ignoreInstruction(instr) and
      type = getResultLanguageType(instr) and
      m = countIndirectionsForCppType(type) and
      indirectionIndex = [1 .. m] and
      not hasIRRepresentationOfIndirectInstruction(instr, indirectionIndex, _, _)
    )
  }
}
