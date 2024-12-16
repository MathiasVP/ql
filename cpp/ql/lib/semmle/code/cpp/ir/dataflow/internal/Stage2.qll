private import cpp as Cpp
private import Base
private import semmle.code.cpp.ir.IR
private import semmle.code.cpp.ir.internal.IRCppLanguage
private import semmle.code.cpp.ir.implementation.raw.internal.TranslatedInitialization
private import semmle.code.cpp.models.interfaces.PointerWrapper
private import DataFlowImplCommon as DataFlowImplCommon
private import semmle.code.cpp.models.interfaces.PartialFlow as PartialFlow
private import semmle.code.cpp.models.interfaces.FunctionInputsAndOutputs as FIO
private import semmle.code.cpp.models.interfaces.DataFlow as DataFlow
private import semmle.code.cpp.models.interfaces.Taint as Taint
private import StageSig
private import Stage0
private import Stage1
private import TypeFlow

module Stage2 implements StageSig {
  private import codeql.ssa.Ssa as SsaImplCommon

  pragma[nomagic]
  private predicate isUnderlyingIndirectionType(Type t) {
    t = any(Stage0Output::Indirection ind).getUnderlyingType()
  }

  /**
   * Holds if the `indirectionIndex`'th dereference of a value of type
   * `cppType` is a type that can be modified (either by modifying the value
   * itself or one of its fields if it's a class type).
   *
   * For example, a value of type `const int* const` cannot be modified
   * at any indirection index (because it's a constant pointer to constant
   * data), and a value of type `int *const *` is modifiable at indirection index
   * 2 only.
   *
   * A value of type `const S2* s2` where `s2` is
   * ```cpp
   * struct S { int x; }
   * ```
   * can be modified at indirection index 1. This is to ensure that we generate
   * a `PostUpdateNode` for the argument corresponding to the `s2` parameter in
   * an example such as:
   * ```cpp
   * void set_field(const S2* s2)
   * {
   *  s2->s->x = 42;
   * }
   * ```
   */
  bindingset[cppType, indirectionIndex]
  pragma[inline_late]
  private predicate impl(CppType cppType, int indirectionIndex) {
    exists(Type pointerType, Type base |
      isUnderlyingIndirectionType(pointerType) and
      cppType.hasUnderlyingType(pointerType, false) and
      base = Stage0Output::getTypeImpl(pointerType, indirectionIndex)
    |
      // The value cannot be modified if it has a const specifier,
      not base.isConst()
      or
      // but in the case of a class type, it may be the case that
      // one of the members was modified.
      exists(base.stripType().(Class).getAField())
    )
  }

  /**
   * Holds if `cppType` is modifiable with an indirection index of at least 1.
   *
   * This predicate factored out into a separate predicate for two reasons:
   * - This predicate needs to be recursive because, if a type is modifiable
   * at indirection `i`, then it's also modifiable at indirection index `i+1`
   * (because the pointer could be completely re-assigned at indirection `i`).
   * - We special-case indirection index `0` so that pointer arguments that can
   * be modified at some index always have a `PostUpdateNode` at indiretion
   * index 0 even though the 0'th indirection can never be modified by a
   * callee.
   */
  private predicate isModifiableAtImplAtLeast1(CppType cppType, int indirectionIndex) {
    indirectionIndex = [1 .. Stage0Output::countIndirectionsForCppType(cppType)] and
    (
      impl(cppType, indirectionIndex)
      or
      // If the `indirectionIndex`'th dereference of a type can be modified
      // then so can the  `indirectionIndex + 1`'th dereference.
      isModifiableAtImplAtLeast1(cppType, indirectionIndex - 1)
    )
  }

  /**
   * Holds if `cppType` is modifiable at indirection index 0.
   *
   * In reality, the 0'th indirection of a pointer (i.e., the pointer itself)
   * can never be modified by a callee, but it is sometimes useful to be able
   * to specify the value of the pointer, as its coming out of a function, as
   * a source of dataflow since the shared library's reverse-read mechanism
   * then ensures that field-flow is accounted for.
   */
  private predicate isModifiableAtImplAt0(CppType cppType) { impl(cppType, 0) }

  /**
   * Holds if `t` is a pointer or reference type that supports at least
   * `indirectionIndex` number of indirections, and the `indirectionIndex`
   * indirection cannot be modfiied by passing a value of `t` to a function.
   */
  private predicate isModifiableAtImpl(CppType cppType, int indirectionIndex) {
    isModifiableAtImplAtLeast1(cppType, indirectionIndex)
    or
    indirectionIndex = 0 and
    isModifiableAtImplAt0(cppType)
  }

  /**
   * Holds if `t` is a type with at least `indirectionIndex` number of
   * indirections, and the `indirectionIndex` indirection can be modified by
   * passing a value of type `t` to a function function.
   */
  bindingset[indirectionIndex]
  predicate isModifiableAt(CppType cppType, int indirectionIndex) {
    isModifiableAtImpl(cppType, indirectionIndex)
    or
    exists(PointerWrapper pw, Type t |
      cppType.hasType(t, _) and
      t.stripType() = pw and
      not pw.pointsToConst()
    )
  }

  /**
   * Holds if the value pointed to by `operand` can potentially be
   * modified be the caller.
   */
  predicate isModifiableByCall(ArgumentOperand operand, int indirectionIndex) {
    exists(CallInstruction call, int index, CppType type |
      indirectionIndex = [0 .. Stage0Output::countIndirectionsForCppType(type)] and
      type = getLanguageType(operand) and
      call.getArgumentOperand(index) = operand and
      if index = -1
      then
        // A qualifier is "modifiable" if:
        // 1. the member function is not const specified, or
        // 2. the member function is `const` specified, but returns a pointer or reference
        // type that is non-const.
        //
        // To see why this is necessary, consider the following function:
        // ```
        // struct C {
        //   void* data_;
        //   void* data() const { return data; }
        // };
        // ...
        // C c;
        // memcpy(c.data(), source, 16)
        // ```
        // the data pointed to by `c.data_` is potentially modified by the call to `memcpy` even though
        // `C::data` has a const specifier. So we further place the restriction that the type returned
        // by `call` should not be of the form `const T*` (for some deeply const type `T`).
        if call.getStaticCallTarget() instanceof Cpp::ConstMemberFunction
        then
          exists(PointerOrArrayOrReferenceType resultType |
            resultType = call.getResultType() and
            not resultType.isDeeplyConstBelow()
          )
        else any()
      else
        // An argument is modifiable if it's a non-const pointer or reference type.
        isModifiableAt(type, indirectionIndex)
    )
  }

  predicate isWrite(Stage0::Node value, Operand address, boolean certain) {
    any(Stage0Output::Indirection ind).isAdditionalWrite(value, address, certain)
    or
    certain = true and
    (
      exists(StoreInstruction store |
        value.asInstruction() = store and
        address = store.getDestinationAddressOperand()
      )
      or
      exists(InitializeParameterInstruction init |
        value.asInstruction() = init and
        address = init.getAnOperand()
      )
      or
      exists(InitializeDynamicAllocationInstruction init |
        value.asInstruction() = init and
        address = init.getAllocationAddressOperand()
      )
      or
      exists(UninitializedInstruction uninitialized |
        value.asInstruction() = uninitialized and
        address = uninitialized.getAnOperand()
      )
    )
  }

  predicate isAdditionalConversionFlow(Operand opFrom, Instruction instrTo) {
    any(Stage0Output::Indirection ind).isAdditionalConversionFlow(opFrom, instrTo)
  }

  /**
   * Holds if `opFrom` is an operand whose value flows to the result of `instrTo`.
   *
   * `isPointerArith` is `true` if `instrTo` is a `PointerArithmeticInstruction` and `opFrom`
   * is the left operand.
   *
   * `additional` is `true` if the conversion is supplied by an implementation of the
   * `Indirection` class. It is sometimes useful to exclude such conversions.
   */
  additional predicate conversionFlow(
    Operand opFrom, Instruction instrTo, boolean isPointerArith, boolean additional
  ) {
    additional = false and
    conversionFlow(opFrom, instrTo, isPointerArith)
    or
    additional = true and
    isPointerArith = false and
    isAdditionalConversionFlow(opFrom, instrTo)
  }

  newtype TBaseSourceVariable =
    // Each IR variable gets its own source variable
    TBaseIRVariable(IRVariable var) or
    // Each allocation gets its own source variable
    TBaseCallVariable(CallInstruction call) { not call.getResultIRType() instanceof IRVoidType }

  abstract private class AbstractBaseSourceVariable extends TBaseSourceVariable {
    /** Gets a textual representation of this element. */
    abstract string toString();

    /** Gets the location of this variable. */
    abstract Location getLocation();

    /** Gets the type of this base source variable. */
    final DataFlowType getType() { this.getLanguageType().hasUnspecifiedType(result, _) }

    /** Gets the `CppType` of this base source variable. */
    abstract CppType getLanguageType();
  }

  final class BaseSourceVariable = AbstractBaseSourceVariable;

  class BaseIRVariable extends AbstractBaseSourceVariable, TBaseIRVariable {
    IRVariable var;

    IRVariable getIRVariable() { result = var }

    BaseIRVariable() { this = TBaseIRVariable(var) }

    override string toString() { result = var.toString() }

    override Location getLocation() { result = var.getLocation() }

    override CppType getLanguageType() { result = var.getLanguageType() }
  }

  class BaseCallVariable extends AbstractBaseSourceVariable, TBaseCallVariable {
    CallInstruction call;

    BaseCallVariable() { this = TBaseCallVariable(call) }

    CallInstruction getCallInstruction() { result = call }

    override string toString() { result = call.toString() }

    override Location getLocation() { result = call.getLocation() }

    override CppType getLanguageType() { result = getResultLanguageType(call) }
  }

  abstract class BaseSourceVariableInstruction extends Instruction {
    /** Gets the base source variable accessed by this instruction. */
    abstract BaseSourceVariable getBaseSourceVariable();
  }

  private class BaseIRVariableInstruction extends BaseSourceVariableInstruction,
    VariableAddressInstruction
  {
    override BaseIRVariable getBaseSourceVariable() {
      result.getIRVariable() = this.getIRVariable()
    }
  }

  private class BaseCallInstruction extends BaseSourceVariableInstruction, CallInstruction {
    override BaseCallVariable getBaseSourceVariable() { result.getCallInstruction() = this }
  }

  /** Holds if `op` is the only use of its defining instruction, and that op is used in a conversation */
  private predicate isConversion(Operand op) {
    exists(Instruction def, Operand use |
      def = op.getDef() and
      use = unique( | | getAUse(def)) and
      conversionFlow(use, _, false)
    )
  }

  /**
   * Holds if `op` is a use of an SSA variable rooted at `base` with `ind` number
   * of indirections.
   *
   * `certain` is `true` if the operand is guaranteed to read the variable, and
   * `indirectionIndex` specifies the number of loads required to read the variable.
   */
  cached
  predicate isUse(
    boolean certain, Operand op, BaseSourceVariableInstruction base, int ind, int indirectionIndex
  ) {
    not ignoreOperand(op) and
    certain = true and
    exists(LanguageType type, int upper, int ind0 |
      type = getLanguageType(op) and
      upper = Stage0Output::countIndirectionsForCppType(type) and
      isUseImpl(op, base, ind0) and
      // Don't count every conversion as their own use. Instead, only the first
      // use (i.e., before any conversions are applied) will count as a use.
      not isConversion(op) and
      ind = ind0 + [0 .. upper] and
      indirectionIndex = ind - ind0
    )
  }

  /**
   * Holds if `operand` is a use of an SSA variable rooted at `base`, and the
   * path from `base` to `operand` passes through `ind` load-like instructions.
   */
  private predicate isUseImpl(Operand operand, BaseSourceVariableInstruction base, int ind) {
    DataFlowImplCommon::forceCachingInSameStage() and
    ind = 0 and
    operand = base.getAUse()
    or
    exists(Operand mid, Instruction instr |
      isUseImpl(mid, base, ind) and
      instr = operand.getDef() and
      conversionFlow(mid, instr, false, _)
    )
    or
    exists(int ind0 |
      exists(Operand address |
        Stage0Output::isDereference(operand.getDef(), address, _) and
        isUseImpl(address, base, ind0)
      )
      or
      isUseImpl(operand.getDef().(InitializeParameterInstruction).getAnOperand(), base, ind0)
    |
      ind0 = ind - 1
    )
  }

  /**
   * Holds if `address` is an address of an SSA variable rooted at `base`,
   * and `instr` is a definition of the SSA variable with `ind` number of indirections.
   *
   * `certain` is `true` if `instr` is guaranteed to write to the variable, and
   * `indirectionIndex` specifies the number of loads required to read the variable
   * after the write operation.
   */
  cached
  predicate isDef(
    boolean certain, Stage0::Node value, Operand address, BaseSourceVariableInstruction base,
    int ind, int indirectionIndex
  ) {
    exists(
      boolean writeIsCertain, boolean addressIsCertain, int ind0, CppType type, int lower, int upper
    |
      isWrite(value, address, writeIsCertain) and
      isDefImpl(address, base, ind0, addressIsCertain) and
      certain = writeIsCertain.booleanAnd(addressIsCertain) and
      type = getLanguageType(address) and
      upper = Stage0Output::countIndirectionsForCppType(type) and
      ind = ind0 + [lower .. upper] and
      indirectionIndex = ind - (ind0 + lower) and
      lower = getMinIndirectionsForType(any(Type t | type.hasUnspecifiedType(t, _)))
    )
  }

  /**
   * Holds if the address computed by `operand` is guaranteed to write
   * to a specific address.
   */
  private predicate isCertainAddress(Operand operand) { isPointerToSingleObject(operand.getDef()) }

  /**
   * Holds if `address` is a use of an SSA variable rooted at `base`, and the
   * path from `base` to `address` passes through `ind` load-like instructions.
   *
   * Note: Unlike `isUseImpl`, this predicate recurses through pointer-arithmetic
   * instructions.
   */
  private predicate isDefImpl(
    Operand operand, BaseSourceVariableInstruction base, int ind, boolean certain
  ) {
    DataFlowImplCommon::forceCachingInSameStage() and
    ind = 0 and
    operand = base.getAUse() and
    (if isCertainAddress(operand) then certain = true else certain = false)
    or
    exists(Operand mid, Instruction instr, boolean certain0, boolean isPointerArith |
      isDefImpl(mid, base, ind, certain0) and
      instr = operand.getDef() and
      conversionFlow(mid, instr, isPointerArith, _) and
      if isPointerArith = true then certain = false else certain = certain0
    )
    or
    exists(Operand address, boolean certain0 |
      Stage0Output::isDereference(operand.getDef(), address, _) and
      isDefImpl(address, base, ind - 1, certain0)
    |
      if isCertainAddress(operand) then certain = certain0 else certain = false
    )
    or
    isDefImpl(operand.getDef().(InitializeParameterInstruction).getAnOperand(), base, ind - 1, _) and
    certain = true
  }

  /**
   * Inputs to the shared SSA library's parameterized module that is shared
   * between the SSA pruning stage, and the final SSA stage.
   */
  module InputSigCommon {
    class BasicBlock extends IRBlock {
      ControlFlowNode getNode(int i) { result = this.getInstruction(i) }

      int length() { result = this.getInstructionCount() }
    }

    class ControlFlowNode = Instruction;

    BasicBlock getImmediateBasicBlockDominator(BasicBlock bb) { result.immediatelyDominates(bb) }

    BasicBlock getABasicBlockSuccessor(BasicBlock bb) { result = bb.getASuccessor() }

    class ExitBasicBlock extends BasicBlock {
      ExitBasicBlock() { this.getLastInstruction() instanceof ExitFunctionInstruction }
    }
  }

  private module SourceVariables {
    cached
    private newtype TSourceVariable =
      TMkSourceVariable(BaseSourceVariable base, int ind) {
        ind = [0 .. Stage0Output::countIndirectionsForCppType(base.getLanguageType()) + 1]
      }

    class SourceVariable extends TSourceVariable {
      BaseSourceVariable base;
      int ind;

      SourceVariable() { this = TMkSourceVariable(base, ind) }

      /** Gets the IR variable associated with this `SourceVariable`, if any. */
      IRVariable getIRVariable() { result = base.(BaseIRVariable).getIRVariable() }

      /**
       * Gets the base source variable (i.e., the variable without any
       * indirections) of this source variable.
       */
      BaseSourceVariable getBaseVariable() { result = base }

      /** Gets a textual representation of this element. */
      string toString() { result = repeatStars(this.getIndirection()) + base.toString() }

      /**
       * Gets the number of loads performed on the base source variable
       * to reach the value of this source variable.
       */
      int getIndirection() { result = ind }

      /** Holds if this variable is a glvalue. */
      predicate isGLValue() { ind = 0 }

      /**
       * Gets the type of this source variable. If `isGLValue()` holds, then
       * the type of this source variable should be thought of as "pointer
       * to `getType()`".
       */
      DataFlowType getType() {
        if this.isGLValue()
        then result = base.getType()
        else result = Stage0Output::getTypeImpl(base.getType(), ind - 1)
      }

      /** Gets the location of this variable. */
      Location getLocation() { result = this.getBaseVariable().getLocation() }
    }
  }

  import SourceVariables

  cached
  private newtype TDefImpl =
    TDefAddressImpl(BaseSourceVariable v) or
    TDirectDefImpl(Operand address, int indirectionIndex) {
      isDef(_, _, address, _, _, indirectionIndex)
    } or
    TGlobalDefImpl(GlobalLikeVariable v, IRFunction f, int indirectionIndex) {
      // Represents the initial "definition" of a global variable when entering
      // a function body.
      isGlobalDefImpl(v, f, _, indirectionIndex)
    }

  private Stage0Output::Indirection getIndirectionForUnspecifiedType(Type t) {
    result.getType() = t
  }

  private predicate underlyingTypeIsModifiableAt(Type underlying, int indirectionIndex) {
    indirectionIndex =
      [1 .. getIndirectionForUnspecifiedType(underlying.getUnspecifiedType())
            .getNumberOfIndirections()] and
    exists(CppType cppType |
      cppType.hasUnderlyingType(underlying, false) and
      isModifiableAt(cppType, indirectionIndex)
    )
  }

  private predicate isGlobalUse(
    GlobalLikeVariable v, IRFunction f, int indirection, int indirectionIndex
  ) {
    // Generate a "global use" at the end of the function body if there's a
    // direct definition somewhere in the body of the function
    indirection =
      min(int cand, VariableAddressInstruction vai |
        vai.getEnclosingIRFunction() = f and
        vai.getAstVariable() = v and
        isDef(_, _, _, vai, cand, indirectionIndex)
      |
        cand
      )
  }

  private predicate isGlobalDefImpl(
    GlobalLikeVariable v, IRFunction f, int indirection, int indirectionIndex
  ) {
    exists(VariableAddressInstruction vai |
      vai.getEnclosingIRFunction() = f and
      vai.getAstVariable() = v and
      isUse(_, _, vai, indirection, indirectionIndex) and
      not isDef(_, _, _, vai, _, indirectionIndex)
    )
  }

  cached
  private newtype TUseImpl =
    TDirectUseImpl(Operand operand, int indirectionIndex) {
      isUse(_, operand, _, _, indirectionIndex) and
      not isDef(true, _, operand, _, _, _)
    } or
    TGlobalUse(GlobalLikeVariable v, IRFunction f, int indirectionIndex) {
      // Represents a final "use" of a global variable to ensure that
      // the assignment to a global variable isn't ruled out as dead.
      isGlobalUse(v, f, _, indirectionIndex)
    } or
    TFinalParameterUse(Parameter p, int indirectionIndex) {
      underlyingTypeIsModifiableAt(p.getUnderlyingType(), indirectionIndex) and
      // Only create an SSA read for the final use of a parameter if there's
      // actually a body of the enclosing function. If there's no function body
      // then we'll never need to flow out of the function anyway.
      p.getFunction().hasDefinition()
    }

  abstract class DefImpl extends TDefImpl {
    int indirectionIndex;

    bindingset[indirectionIndex]
    DefImpl() { any() }

    /** Gets a textual representation of this element. */
    abstract string toString();

    /** Gets the block of this definition or use. */
    final IRBlock getBlock() { this.hasIndexInBlock(result, _) }

    /** Holds if this definition or use has index `index` in block `block`. */
    abstract predicate hasIndexInBlock(IRBlock block, int index);

    /**
     * Holds if this definition (or use) has index `index` in block `block`,
     * and is a definition (or use) of the variable `sv`
     */
    final predicate hasIndexInBlock(IRBlock block, int index, SourceVariable sv) {
      this.hasIndexInBlock(block, index) and
      sv = this.getSourceVariable()
    }

    /** Gets the location of this element. */
    abstract Location getLocation();

    /** Gets the indirection index of this definition. */
    final int getIndirectionIndex() { result = indirectionIndex }

    /**
     * Gets the index (i.e., the number of loads required) of this
     * definition or use.
     *
     * Note that this is _not_ the definition's (or use's) index in
     * the enclosing basic block. To obtain this index, use
     * `DefOrUseImpl::hasIndexInBlock/2` or `DefOrUseImpl::hasIndexInBlock/3`.
     */
    abstract int getIndirection();

    /**
     * Gets the base source variable (i.e., the variable without
     * any indirection) of this definition or use.
     */
    abstract BaseSourceVariable getBaseSourceVariable();

    /** Gets the variable that is defined or used. */
    SourceVariable getSourceVariable() {
      exists(BaseSourceVariable v, int indirection |
        sourceVariableHasBaseAndIndex(result, v, indirection) and
        defHasSourceVariable(this, v, indirection)
      )
    }

    abstract predicate isCertain();

    abstract Stage0::Node getValue();

    Operand getAddressOperand() { none() }
  }

  abstract class UseImpl extends TUseImpl {
    int indirectionIndex;

    bindingset[indirectionIndex]
    UseImpl() { any() }

    /** Gets the node associated with this use. */
    abstract Node getNode();

    /** Gets a textual representation of this element. */
    abstract string toString();

    /** Gets the block of this definition or use. */
    final IRBlock getBlock() { this.hasIndexInBlock(result, _) }

    /** Holds if this definition or use has index `index` in block `block`. */
    abstract predicate hasIndexInBlock(IRBlock block, int index);

    /**
     * Holds if this definition (or use) has index `index` in block `block`,
     * and is a definition (or use) of the variable `sv`
     */
    final predicate hasIndexInBlock(IRBlock block, int index, SourceVariable sv) {
      this.hasIndexInBlock(block, index) and
      sv = this.getSourceVariable()
    }

    /** Gets the location of this element. */
    abstract Location getLocation();

    /**
     * Gets the index (i.e., the number of loads required) of this
     * definition or use.
     *
     * Note that this is _not_ the definition's (or use's) index in
     * the enclosing basic block. To obtain this index, use
     * `DefOrUseImpl::hasIndexInBlock/2` or `DefOrUseImpl::hasIndexInBlock/3`.
     */
    abstract int getIndirection();

    /** Gets the indirection index of this use. */
    final int getIndirectionIndex() { result = indirectionIndex }

    /**
     * Gets the base source variable (i.e., the variable without
     * any indirection) of this definition or use.
     */
    abstract BaseSourceVariable getBaseSourceVariable();

    /** Gets the variable that is defined or used. */
    SourceVariable getSourceVariable() {
      exists(BaseSourceVariable v, int indirection |
        sourceVariableHasBaseAndIndex(result, v, indirection) and
        useHasSourceVariable(this, v, indirection)
      )
    }

    /**
     * Holds if this use is guaranteed to read the
     * associated variable.
     */
    abstract predicate isCertain();
  }

  pragma[noinline]
  private predicate defHasSourceVariable(DefImpl def, BaseSourceVariable bv, int ind) {
    bv = def.getBaseSourceVariable() and
    ind = def.getIndirection()
  }

  pragma[noinline]
  private predicate useHasSourceVariable(UseImpl use, BaseSourceVariable bv, int ind) {
    bv = use.getBaseSourceVariable() and
    ind = use.getIndirection()
  }

  pragma[noinline]
  private predicate sourceVariableHasBaseAndIndex(SourceVariable v, BaseSourceVariable bv, int ind) {
    v.getBaseVariable() = bv and
    v.getIndirection() = ind
  }

  /**
   * Gets the instruction that computes the address that's used to
   * initialize `v`.
   */
  private Instruction getInitializationTargetAddress(IRVariable v) {
    exists(TranslatedVariableInitialization init |
      init.getIRVariable() = v and
      result = init.getTargetAddress()
    )
  }

  /** An initial definition of an SSA variable address. */
  abstract private class DefAddressImpl extends DefImpl, TDefAddressImpl {
    BaseSourceVariable v;

    DefAddressImpl() {
      this = TDefAddressImpl(v) and
      indirectionIndex = 0
    }

    override string toString() { result = "Def of &" + v.toString() }

    final override int getIndirection() { result = 0 }

    final override predicate isCertain() { any() }

    final override Stage0::Node getValue() { none() }

    override Location getLocation() { result = v.getLocation() }

    final override SourceVariable getSourceVariable() {
      result.getBaseVariable() = v and
      result.getIndirection() = 0
    }

    final override BaseSourceVariable getBaseSourceVariable() { result = v }
  }

  private class DefVariableAddressImpl extends DefAddressImpl {
    override BaseIRVariable v;

    final override predicate hasIndexInBlock(IRBlock block, int index) {
      exists(IRVariable var | var = v.getIRVariable() |
        block.getInstruction(index) = getInitializationTargetAddress(var)
        or
        // If there is no translatated element that does initialization of the
        // variable we place the SSA definition at the entry block of the function.
        not exists(getInitializationTargetAddress(var)) and
        block = var.getEnclosingIRFunction().getEntryBlock() and
        index = 0
      )
    }
  }

  private class DefCallAddressImpl extends DefAddressImpl {
    override BaseCallVariable v;

    final override predicate hasIndexInBlock(IRBlock block, int index) {
      block.getInstruction(index) = v.getCallInstruction()
    }
  }

  private class DirectDef extends DefImpl, TDirectDefImpl {
    Operand address;

    DirectDef() { this = TDirectDefImpl(address, indirectionIndex) }

    override Location getLocation() { result = this.getAddressOperand().getUse().getLocation() }

    final override predicate hasIndexInBlock(IRBlock block, int index) {
      this.getAddressOperand().getUse() = block.getInstruction(index)
    }

    override string toString() { result = "Def of " + this.getSourceVariable() }

    override Operand getAddressOperand() { result = address }

    private BaseSourceVariableInstruction getBase() {
      isDef(_, _, address, result, _, indirectionIndex)
    }

    override BaseSourceVariable getBaseSourceVariable() {
      result = this.getBase().getBaseSourceVariable()
    }

    override int getIndirection() { isDef(_, _, address, _, result, indirectionIndex) }

    override Stage0::Node getValue() { isDef(_, result, address, _, _, _) }

    override predicate isCertain() { isDef(true, _, address, _, _, indirectionIndex) }
  }

  private class DirectUseImpl extends UseImpl, TDirectUseImpl {
    Operand operand;

    DirectUseImpl() { this = TDirectUseImpl(operand, indirectionIndex) }

    override string toString() { result = "Use of " + this.getSourceVariable() }

    final override predicate hasIndexInBlock(IRBlock block, int index) {
      // See the comment in `ssa0`'s `OperandBasedUse` for an explanation of this
      // predicate's implementation.
      if this.getBase().getAst() = any(Cpp::PostfixCrementOperation c).getOperand()
      then
        exists(Operand op, int indirection, Instruction base |
          indirection = this.getIndirection() and
          base = this.getBase() and
          op =
            min(Operand cand, int i |
              isUse(_, cand, base, indirection, indirectionIndex) and
              block.getInstruction(i) = cand.getUse()
            |
              cand order by i
            ) and
          block.getInstruction(index) = op.getUse()
        )
      else operand.getUse() = block.getInstruction(index)
    }

    private BaseSourceVariableInstruction getBase() {
      isUse(_, operand, result, _, indirectionIndex)
    }

    override BaseSourceVariable getBaseSourceVariable() {
      result = this.getBase().getBaseSourceVariable()
    }

    final Operand getOperand() { result = operand }

    final override Location getLocation() { result = operand.getLocation() }

    override int getIndirection() { isUse(_, operand, _, result, indirectionIndex) }

    override predicate isCertain() { isUse(true, operand, _, _, indirectionIndex) }

    override Node getNode() { nodeHasOperand(result, operand, indirectionIndex) }
  }

  pragma[nomagic]
  private predicate finalParameterNodeHasParameterAndIndex(
    FinalParameterNode n, Parameter p, int indirectionIndex
  ) {
    n.getParameter() = p and
    n.getIndirectionIndex() = indirectionIndex
  }

  class FinalParameterUse extends UseImpl, TFinalParameterUse {
    Parameter p;

    FinalParameterUse() { this = TFinalParameterUse(p, indirectionIndex) }

    override string toString() { result = "Use of " + p.toString() }

    Parameter getParameter() { result = p }

    int getArgumentIndex() { result = p.getIndex() }

    override Node getNode() { finalParameterNodeHasParameterAndIndex(result, p, indirectionIndex) }

    override int getIndirection() { result = indirectionIndex + 1 }

    override predicate isCertain() { any() }

    override predicate hasIndexInBlock(IRBlock block, int index) {
      // Ideally, this should always be a `ReturnInstruction`, but if
      // someone forgets to write a `return` statement in a function
      // with a non-void return type we generate an `UnreachedInstruction`.
      // In this case we still want to generate flow out of such functions
      // if they write to a parameter. So we pick the index of the
      // `UnreachedInstruction` as the index of this use.
      // Note that a function may have both a `ReturnInstruction` and an
      // `UnreachedInstruction`. If that's the case this predicate will
      // return multiple results. I don't think this is detrimental to
      // performance, however.
      exists(Instruction return |
        return instanceof ReturnInstruction or
        return instanceof UnreachedInstruction
      |
        block.getInstruction(index) = return and
        return.getEnclosingFunction() = p.getFunction()
      )
    }

    override Location getLocation() {
      // Parameters can have multiple locations. When there's a unique location we use
      // that one, but if multiple locations exist we default to an unknown location.
      result = unique( | | p.getLocation())
      or
      not exists(unique( | | p.getLocation())) and
      result instanceof UnknownDefaultLocation
    }

    override BaseIRVariable getBaseSourceVariable() { result.getIRVariable().getAst() = p }
  }

  /**
   * INTERNAL: do not use.
   *
   * A node representing the value of a global variable just after entering
   * a function body.
   */
  class InitialGlobalValue extends Node, TInitialGlobalValue {
    GlobalDef globalDef;

    InitialGlobalValue() { this = TInitialGlobalValue(globalDef) }

    final override Instruction asInstruction() { none() }

    final override Operand asOperand() { none() }

    /** Gets the underlying SSA definition. */
    GlobalDef getGlobalDef() { result = globalDef }

    override Declaration getEnclosingCallable() { result = this.getFunction() }

    override Declaration getFunction() { result = globalDef.getIRFunction().getFunction() }

    final override predicate isGLValue() { globalDef.getIndirectionIndex() = 0 }

    override DataFlowType getType() {
      exists(DataFlowType type |
        type = globalDef.getUnderlyingType() and
        if this.isGLValue()
        then result = type
        else result = Stage0Output::getTypeImpl(type, globalDef.getIndirectionIndex() - 1)
      )
    }

    final override Location getLocation() { result = globalDef.getLocation() }

    final override string stars() { result = repeatStars(globalDef.getIndirectionIndex()) }

    final override predicate hasIndexInBlock(IRBlock block, int index) {
      globalDef.hasIndexInBlock(block, index, _)
    }

    override string toString() { result = globalDef.toString() }
  }

  /**
   * INTERNAL: do not use.
   *
   * A node representing the value of a global variable just before returning
   * from a function body.
   */
  class FinalGlobalValue extends Node, TFinalGlobalValue {
    GlobalUse globalUse;

    FinalGlobalValue() { this = TFinalGlobalValue(globalUse) }

    final override Instruction asInstruction() { none() }

    final override Operand asOperand() { none() }

    /** Gets the underlying SSA use. */
    GlobalUse getGlobalUse() { result = globalUse }

    override Declaration getEnclosingCallable() { result = this.getFunction() }

    override Declaration getFunction() { result = globalUse.getIRFunction().getFunction() }

    override DataFlowType getType() {
      exists(int indirectionIndex |
        indirectionIndex = globalUse.getIndirectionIndex() and
        result = Stage0Output::getTypeImpl(globalUse.getUnderlyingType(), indirectionIndex - 1)
      )
    }

    final override Location getLocation() { result = globalUse.getLocation() }

    final override string stars() { result = repeatStars(globalUse.getIndirectionIndex()) }

    final override predicate isGLValue() { none() }

    final override predicate hasIndexInBlock(IRBlock block, int index) {
      globalUse.hasIndexInBlock(block, index)
    }

    override string toString() { result = globalUse.toString() }
  }

  /**
   * A use that models a synthetic "last use" of a global variable just before a
   * function returns.
   *
   * We model global variable flow by:
   * - Inserting a last use of any global variable that's modified by a function
   * - Flowing from the last use to the `VariableNode` that represents the global
   *   variable.
   * - Flowing from the `VariableNode` to an "initial def" of the global variable
   * in any function that may read the global variable.
   * - Flowing from the initial definition to any subsequent uses of the global
   *   variable in the function body.
   *
   * For example, consider the following pair of functions:
   * ```cpp
   * int global;
   * int source();
   * void sink(int);
   *
   * void set_global() {
   *   global = source();
   * }
   *
   * void read_global() {
   *  sink(global);
   * }
   * ```
   * we insert global uses and defs so that (from the point-of-view of dataflow)
   * the above scenario looks like:
   * ```cpp
   * int global; // (1)
   * int source();
   * void sink(int);
   *
   * void set_global() {
   *   global = source();
   *   __global_use(global); // (2)
   * }
   *
   * void read_global() {
   *  global = __global_def; // (3)
   *  sink(global); // (4)
   * }
   * ```
   * and flow from `source()` to the argument of `sink` is then modeled as
   * follows:
   * 1. Flow from `source()` to `(2)` (via SSA).
   * 2. Flow from `(2)` to `(1)` (via a `jumpStep`).
   * 3. Flow from `(1)` to `(3)` (via a `jumpStep`).
   * 4. Flow from `(3)` to `(4)` (via SSA).
   */
  class GlobalUse extends UseImpl, TGlobalUse {
    GlobalLikeVariable global;
    IRFunction f;

    GlobalUse() { this = TGlobalUse(global, f, indirectionIndex) }

    override string toString() { result = "Use of " + global }

    override FinalGlobalValue getNode() { result.getGlobalUse() = this }

    override int getIndirection() { isGlobalUse(global, f, result, indirectionIndex) }

    /** Gets the global variable associated with this use. */
    GlobalLikeVariable getVariable() { result = global }

    /** Gets the `IRFunction` whose body is exited from after this use. */
    IRFunction getIRFunction() { result = f }

    final override predicate hasIndexInBlock(IRBlock block, int index) {
      // Similar to the `FinalParameterUse` case, we want to generate flow out of
      // globals at any exit so that we can flow out of non-returning functions.
      // Obviously this isn't correct as we can't actually flow but the global flow
      // requires this if we want to flow into children.
      exists(Instruction return |
        return instanceof ReturnInstruction or
        return instanceof UnreachedInstruction
      |
        block.getInstruction(index) = return and
        return.getEnclosingIRFunction() = f
      )
    }

    override BaseSourceVariable getBaseSourceVariable() {
      baseSourceVariableIsGlobal(result, global, f)
    }

    final override Location getLocation() { result = f.getLocation() }

    /**
     * Gets the type of this use after specifiers have been deeply stripped
     * and typedefs have been resolved.
     */
    Type getUnspecifiedType() { result = global.getUnspecifiedType() }

    /**
     * Gets the type of this use, after typedefs have been resolved.
     */
    Type getUnderlyingType() { result = global.getUnderlyingType() }

    override predicate isCertain() { any() }
  }

  /**
   * A definition that models a synthetic "initial definition" of a global
   * variable just after the function entry point.
   *
   * See the QLDoc for `GlobalUse` for how this is used.
   */
  class GlobalDefImpl extends DefImpl, TGlobalDefImpl {
    GlobalLikeVariable global;
    IRFunction f;

    GlobalDefImpl() { this = TGlobalDefImpl(global, f, indirectionIndex) }

    /** Gets the global variable associated with this definition. */
    GlobalLikeVariable getVariable() { result = global }

    /** Gets the `IRFunction` whose body is evaluated after this definition. */
    IRFunction getIRFunction() { result = f }

    /** Holds if this definition or use has index `index` in block `block`. */
    final override predicate hasIndexInBlock(IRBlock block, int index) {
      exists(EnterFunctionInstruction enter |
        enter = f.getEnterFunctionInstruction() and
        block.getInstruction(index) = enter
      )
    }

    /** Gets the global variable associated with this definition. */
    override BaseSourceVariable getBaseSourceVariable() {
      baseSourceVariableIsGlobal(result, global, f)
    }

    override int getIndirection() { result = indirectionIndex }

    override Stage0::Node getValue() { none() }

    override predicate isCertain() { any() }

    /**
     * Gets the type of this definition after specifiers have been deeply
     * stripped and typedefs have been resolved.
     */
    Type getUnspecifiedType() { result = global.getUnspecifiedType() }

    /**
     * Gets the type of this definition, after typedefs have been resolved.
     */
    Type getUnderlyingType() { result = global.getUnderlyingType() }

    override string toString() { result = "Def of " + this.getSourceVariable() }

    override Location getLocation() { result = f.getLocation() }
  }

  /**
   * Holds if there is a definition or access at index `i1` in basic block `bb1`
   * and the next subsequent read is at index `i2` in basic block `bb2`.
   */
  predicate adjacentDefRead(IRBlock bb1, int i1, SourceVariable sv, IRBlock bb2, int i2) {
    SsaCached::adjacentDefReadExt(_, sv, bb1, i1, bb2, i2)
  }

  predicate useToNode(IRBlock bb, int i, SourceVariable sv, Node nodeTo) {
    exists(UseImpl use |
      use.hasIndexInBlock(bb, i, sv) and
      nodeTo = use.getNode()
    )
  }

  /**
   * INTERNAL: Do not use.
   *
   * Holds if `node` is the node that corresponds to the definition of `def`.
   */
  predicate defToNode(Node node, Def def, SourceVariable sv, IRBlock bb, int i, boolean uncertain) {
    def.hasIndexInBlock(bb, i, sv) and
    (
      nodeHasOperand(node, def.getValue().asOperand(), def.getIndirectionIndex())
      or
      nodeHasInstruction(node, def.getValue().asInstruction(), def.getIndirectionIndex())
      or
      node.(InitialGlobalValue).getGlobalDef() = def
    ) and
    if def.isCertain() then uncertain = false else uncertain = true
  }

  /**
   * INTERNAL: Do not use.
   *
   * Holds if `node` is the node that corresponds to the definition or use at
   * index `i` in block `bb` of `sv`.
   *
   * `uncertain` is `true` if this is an uncertain definition.
   */
  predicate nodeToDefOrUse(Node node, SourceVariable sv, IRBlock bb, int i, boolean uncertain) {
    defToNode(node, _, sv, bb, i, uncertain)
    or
    // Node -> Use
    useToNode(bb, i, sv, node) and
    uncertain = false
  }

  /**
   * Perform a single conversion-like step from `nFrom` to `nTo`. This relation
   * only holds when there is no use-use relation out of `nTo`.
   */
  private predicate indirectConversionFlowStep(Node nFrom, Node nTo) {
    not exists(SourceVariable sv, IRBlock bb2, int i2 |
      useToNode(bb2, i2, sv, nTo) and
      adjacentDefRead(bb2, i2, sv, _, _)
    ) and
    exists(Operand op1, Operand op2, int indirectionIndex, Instruction instr |
      hasOperandAndIndex(nFrom, op1, pragma[only_bind_into](indirectionIndex)) and
      hasOperandAndIndex(nTo, op2, pragma[only_bind_into](indirectionIndex)) and
      instr = op2.getDef() and
      conversionFlow(op1, instr, _, _)
    )
  }

  /**
   * Holds if `node` is a phi input node that should receive flow from the
   * definition to (or use of) `sv` at `(bb1, i1)`.
   */
  private predicate phiToNode(SsaPhiInputNode node, SourceVariable sv, IRBlock bb1, int i1) {
    exists(PhiNode phi, IRBlock input |
      phi.hasInputFromBlock(_, sv, bb1, i1, input) and
      node.getPhiNode() = phi and
      node.getBlock() = input
    )
  }

  /**
   * Holds if there should be flow from `nodeFrom` to `nodeTo` because
   * `nodeFrom` is a definition or use of `sv` at index `i1` at basic
   * block `bb1`.
   *
   * `uncertain` is `true` if `(bb1, i1)` is a definition, and that definition
   * is _not_ guaranteed to overwrite the entire allocation.
   */
  private predicate ssaFlowImpl(
    IRBlock bb1, int i1, SourceVariable sv, Node nodeFrom, Node nodeTo, boolean uncertain
  ) {
    nodeToDefOrUse(nodeFrom, sv, bb1, i1, uncertain) and
    (
      exists(IRBlock bb2, int i2 |
        adjacentDefRead(bb1, i1, sv, bb2, i2) and
        useToNode(bb2, i2, sv, nodeTo)
      )
      or
      phiToNode(nodeTo, sv, bb1, i1)
    ) and
    nodeFrom != nodeTo
  }

  /** Gets a node that represents the prior definition of `node`. */
  private Node getAPriorDefinition(DefinitionExt next) {
    exists(IRBlock bb, int i, SourceVariable sv |
      SsaCached::lastRefRedefExt(_, pragma[only_bind_into](sv), pragma[only_bind_into](bb),
        pragma[only_bind_into](i), _, next) and
      nodeToDefOrUse(result, sv, bb, i, _)
    )
  }

  private predicate inOut(FIO::FunctionInput input, FIO::FunctionOutput output) {
    exists(int indirectionIndex |
      input.isQualifierObject(indirectionIndex) and
      output.isQualifierObject(indirectionIndex)
      or
      exists(int i |
        input.isParameterDeref(i, indirectionIndex) and
        output.isParameterDeref(i, indirectionIndex)
      )
    )
  }

  private class CallOutNode = Stage1OutNode;

  private CallOutNode getIndirectReturnOutNode(CallInstruction call, int d) {
    d > 0 and
    result.getCall() = call and
    result.getReturnKind().getIndirectionIndex() = d
  }

  /**
   * Gets the instruction that goes into `input` for `call`.
   */
  Node callInput(CallInstruction call, FIO::FunctionInput input) {
    // An argument or qualifier
    exists(int index |
      result.asOperand() = call.getArgumentOperand(index) and
      input.isParameterOrQualifierAddress(index)
    )
    or
    // A value pointed to by an argument or qualifier
    exists(int index, int indirectionIndex |
      hasOperandAndIndex(result, call.getArgumentOperand(index), indirectionIndex) and
      input.isParameterDerefOrQualifierObject(index, indirectionIndex)
    )
    or
    exists(int ind |
      result = getIndirectReturnOutNode(call, ind) and
      input.isReturnValueDeref(ind)
    )
  }

  /**
   * Gets the node that represents the output of `call` with kind `output` at
   * indirection index `indirectionIndex`.
   */
  Node callOutputWithIndirectionIndex(
    CallInstruction call, FIO::FunctionOutput output, int indirectionIndex
  ) {
    // The return value
    exists(CallOutNode callOut |
      result = callOut and
      callOut.getCall() = call and
      callOut.getReturnKind().getIndirectionIndex() = 0 and
      output.isReturnValue() and
      indirectionIndex = 0
    )
    or
    // The side effect of a call on the value pointed to by an argument or qualifier
    exists(int index, ArgumentOutNode argOut |
      result = argOut and
      argOut.getArgumentIndex() = index and
      argOut.getIndirectionIndex() = indirectionIndex - 1 and
      argOut.getCallInstruction() = call and
      output.isParameterDerefOrQualifierObject(index, indirectionIndex - 1)
    )
    or
    result = getIndirectReturnOutNode(call, indirectionIndex) and
    output.isReturnValueDeref(indirectionIndex)
  }

  Node callOutput(CallInstruction call, FIO::FunctionOutput output) {
    result = callOutputWithIndirectionIndex(call, output, _)
  }

  /**
   * Holds if there should not be use-use flow out of `n`. That is, `n` is
   * an out-barrier to use-use flow. This includes:
   *
   * - an input to a call that would be assumed to have use-use flow to the same
   *   argument as an output, but this flow should be blocked because the
   *   function is modeled with another flow to that output (for example the
   *   first argument of `strcpy`).
   * - a conversion that flows to such an input.
   */
  private predicate modeledFlowBarrier(Node n) {
    exists(
      FIO::FunctionInput input, FIO::FunctionOutput output, CallInstruction call,
      PartialFlow::PartialFlowFunction partialFlowFunc
    |
      n = callInput(call, input) and
      inOut(input, output) and
      exists(callOutput(call, output)) and
      partialFlowFunc = call.getStaticCallTarget() and
      not partialFlowFunc.isPartialWrite(output)
    |
      call.getStaticCallTarget().(DataFlow::DataFlowFunction).hasDataFlow(_, output)
      or
      call.getStaticCallTarget().(Taint::TaintFunction).hasTaintFlow(_, output)
    )
    or
    exists(Operand operand, Instruction instr, Node n0, int indirectionIndex |
      modeledFlowBarrier(n0) and
      nodeHasInstruction(n0, instr, indirectionIndex) and
      conversionFlow(operand, instr, false, _) and
      nodeHasOperand(n, operand, indirectionIndex)
    )
  }

  /** Holds if there is def-use or use-use flow from `nodeFrom` to `nodeTo`. */
  predicate ssaFlow(Node nodeFrom, Node nodeTo) {
    exists(Node nFrom, boolean uncertain, IRBlock bb, int i, SourceVariable sv |
      ssaFlowImpl(bb, i, sv, nFrom, nodeTo, uncertain) and
      not modeledFlowBarrier(nFrom) and
      nodeFrom != nodeTo
    |
      if uncertain = true
      then
        nodeFrom =
          [nFrom, getAPriorDefinition(any(DefinitionExt next | next.definesAt(sv, bb, i, _)))]
      else nodeFrom = nFrom
    )
  }

  // signature module PostUpdateFlowInputSig {
  //   class Node2;
  //   class PostUpdateNode {
  //     Node2 getPreUpdateNode();
  //   }
  //   Node inject(Node2 pre);
  // }
  // private module Stage2PostUpdateFlowInput implements PostUpdateFlowInputSig {
  //   class Node2 = Node;
  //   class PostUpdateNode = Stage2::PostUpdateNode;
  //   Node inject(Node2 pre) { result = pre }
  // }
  // module PostUpdateFlow<PostUpdateFlowInputSig Input> {
  private predicate isArgumentOfCallableInstruction(DataFlowCall call, Instruction instr) {
    isArgumentOfCallableOperand(call, unique( | | getAUse(instr)))
  }

  private predicate isArgumentOfCallableOperand(DataFlowCall call, Operand operand) {
    operand = call.getArgumentOperand(_)
    or
    exists(FieldAddressInstruction fai |
      fai.getObjectAddressOperand() = operand and
      isArgumentOfCallableInstruction(call, fai)
    )
    or
    exists(Instruction deref |
      isArgumentOfCallableInstruction(call, deref) and
      Stage0Output::isDereference(deref, operand, _)
    )
    or
    exists(Instruction instr |
      isArgumentOfCallableInstruction(call, instr) and
      conversionFlow(operand, instr, _, _)
    )
  }

  private predicate isArgumentOfCallable(DataFlowCall call, Node n) {
    isArgumentOfCallableOperand(call, n.asOperand())
    or
    exists(Operand op |
      n.(IndirectOperandNode).hasOperandAndIndirectionIndex(op, _) and
      isArgumentOfCallableOperand(call, op)
    )
    or
    exists(Instruction instr |
      n.(IndirectInstructionNode).hasInstructionAndIndirectionIndex(instr, _) and
      isArgumentOfCallableInstruction(call, instr)
    )
  }

  /**
   * Holds if there is use-use flow from `pun`'s pre-update node to `n`.
   */
  private predicate postUpdateNodeToFirstUse(/*Input::*/ PostUpdateNode pun, Node n) {
    // We cannot mark a `PointerArithmeticInstruction` that computes an offset
    // based on some SSA
    // variable `x` as a use of `x` since this creates taint-flow in the
    // following example:
    // ```c
    // int x = array[source]
    // sink(*array)
    // ```
    // This is because `source` would flow from the operand of `PointerArithmetic`
    // instruction to the result of the instruction, and into the `IndirectOperand`
    // that represents the value of `*array`. Then, via use-use flow, flow will
    // arrive at `*array` in `sink(*array)`.
    // So this predicate recurses back along conversions and `PointerArithmetic`
    // instructions to find the first use that has provides use-use flow, and
    // uses that target as the target of the `nodeFrom`.
    exists(Node adjusted, IRBlock bb1, int i1, SourceVariable sv |
      indirectConversionFlowStep*(adjusted, /*Input::inject*/ pun.getPreUpdateNode()) and
      useToNode(bb1, i1, sv, adjusted)
    |
      exists(IRBlock bb2, int i2 |
        adjacentDefRead(bb1, i1, sv, bb2, i2) and
        useToNode(bb2, i2, sv, n)
      )
      or
      phiToNode(n, sv, bb1, i1)
    )
  }

  private predicate stepUntilNotInCall(DataFlowCall call, Node n1, Node n2) {
    isArgumentOfCallable(call, n1) and
    exists(Node mid | ssaFlowImpl(_, _, _, n1, mid, _) |
      isArgumentOfCallable(call, mid) and
      stepUntilNotInCall(call, mid, n2)
      or
      not isArgumentOfCallable(call, mid) and
      mid = n2
    )
  }

  bindingset[n1, n2]
  pragma[inline_late]
  private predicate isArgumentOfSameCall(DataFlowCall call, Node n1, Node n2) {
    isArgumentOfCallable(call, n1) and isArgumentOfCallable(call, n2)
  }

  /**
   * Holds if there is def-use or use-use flow from `pun` to `nodeTo`.
   *
   * Note: This is more complex than it sounds. Consider a call such as:
   * ```cpp
   * write_first_argument(x, x);
   * sink(x);
   * ```
   * Assume flow comes out of the first argument to `write_first_argument`. We
   * don't want flow to go to the `x` that's also an argument to
   * `write_first_argument` (because we just flowed out of that function, and we
   * don't want to flow back into it again).
   *
   * We do, however, want flow from the output argument to `x` on the next line, and
   * similarly we want flow from the second argument of `write_first_argument` to `x`
   * on the next line.
   */
  predicate postUpdateFlow(/*Input::*/ PostUpdateNode pun, Node nodeTo) {
    exists(Node preUpdate, Node mid |
      preUpdate = /*Input::inject*/ pun.getPreUpdateNode() and
      postUpdateNodeToFirstUse(pun, mid)
    |
      exists(DataFlowCall call |
        isArgumentOfSameCall(call, preUpdate, mid) and
        stepUntilNotInCall(call, mid, nodeTo)
      )
      or
      not isArgumentOfSameCall(_, preUpdate, mid) and
      nodeTo = mid
    )
  }

  // }
  // private import PostUpdateFlow<Stage2PostUpdateFlowInput>
  /** Holds if `nodeTo` receives flow from the phi node `nodeFrom`. */
  predicate fromPhiNode(SsaPhiNode nodeFrom, Node nodeTo) {
    exists(PhiNode phi, SourceVariable sv, IRBlock bb1, int i1 |
      phi = nodeFrom.getPhiNode() and
      phi.definesAt(sv, bb1, i1, _)
    |
      exists(IRBlock bb2, int i2 |
        adjacentDefRead(bb1, i1, sv, bb2, i2) and
        useToNode(bb2, i2, sv, nodeTo)
      )
      or
      phiToNode(nodeTo, sv, bb1, i1)
    )
  }

  private predicate baseSourceVariableIsGlobal(
    BaseIRVariable base, GlobalLikeVariable global, IRFunction func
  ) {
    exists(IRVariable irVar |
      irVar = base.getIRVariable() and
      irVar.getEnclosingIRFunction() = func and
      global = irVar.getAst() and
      not irVar instanceof IRDynamicInitializationFlag
    )
  }

  private module SsaInput implements SsaImplCommon::InputSig<Location> {
    import InputSigCommon
    import SourceVariables

    /**
     * Holds if the `i`'th write in block `bb` writes to the variable `v`.
     * `certain` is `true` if the write is guaranteed to overwrite the entire variable.
     */
    predicate variableWrite(BasicBlock bb, int i, SourceVariable v, boolean certain) {
      DataFlowImplCommon::forceCachingInSameStage() and
      (
        exists(DefImpl def | def.hasIndexInBlock(bb, i, v) |
          if def.isCertain() then certain = true else certain = false
        )
        or
        exists(GlobalDefImpl global |
          global.hasIndexInBlock(bb, i, v) and
          certain = true
        )
      )
    }

    /**
     * Holds if the `i`'th read in block `bb` reads to the variable `v`.
     * `certain` is `true` if the read is guaranteed. For C++, this is always the case.
     */
    predicate variableRead(BasicBlock bb, int i, SourceVariable v, boolean certain) {
      exists(UseImpl use | use.hasIndexInBlock(bb, i, v) |
        if use.isCertain() then certain = true else certain = false
      )
      or
      exists(GlobalUse global |
        global.hasIndexInBlock(bb, i, v) and
        certain = true
      )
    }
  }

  cached
  private newtype TSsaDef =
    TDef(DefinitionExt def) or
    TPhi(PhiNode phi)

  abstract private class SsaDef extends TSsaDef {
    /** Gets a textual representation of this element. */
    string toString() { none() }

    /** Gets the underlying non-phi definition or use. */
    DefinitionExt asDef() { none() }

    /** Gets the underlying phi node. */
    PhiNode asPhi() { none() }

    /** Gets the location of this element. */
    abstract Location getLocation();
  }

  abstract class Def extends SsaDef, TDef {
    DefinitionExt def;

    Def() { this = TDef(def) }

    final override DefinitionExt asDef() { result = def }

    /** Gets the source variable underlying this SSA definition. */
    final SourceVariable getSourceVariable() { result = def.getSourceVariable() }

    override string toString() { result = def.toString() }

    /**
     * Holds if this definition (or use) has index `index` in block `block`,
     * and is a definition (or use) of the variable `sv`.
     */
    predicate hasIndexInBlock(IRBlock block, int index, SourceVariable sv) {
      def.definesAt(sv, block, index, _)
    }

    /** Gets the value written by this definition, if any. */
    Stage0::Node getValue() { none() }

    /**
     * Holds if this definition is guaranteed to overwrite the entire
     * destination's allocation.
     */
    abstract predicate isCertain();

    /** Gets the address operand written to by this definition. */
    Operand getAddressOperand() { none() }

    /** Gets the address written to by this definition. */
    final Instruction getAddress() { result = this.getAddressOperand().getDef() }

    /** Gets the indirection index of this definition. */
    abstract int getIndirectionIndex();

    /**
     * Gets the indirection level that this definition is writing to.
     * For instance, `x = y` is a definition of `x` at indirection level 1 and
     * `*x = y` is a definition of `x` at indirection level 2.
     */
    abstract int getIndirection();

    /**
     * Gets a definition that ultimately defines this SSA definition and is not
     * itself a phi node.
     */
    Def getAnUltimateDefinition() { result.asDef() = def.getAnUltimateDefinition() }
  }

  private predicate isGlobal(DefinitionExt def, GlobalDefImpl global) {
    exists(SourceVariable sv, IRBlock bb, int i |
      def.definesAt(sv, bb, i, _) and
      global.hasIndexInBlock(bb, i, sv)
    )
  }

  private class NonGlobalDef extends Def {
    NonGlobalDef() { not isGlobal(def, _) }

    final override Location getLocation() { result = this.getImpl().getLocation() }

    private DefImpl getImpl() {
      exists(SourceVariable sv, IRBlock bb, int i |
        this.hasIndexInBlock(bb, i, sv) and
        result.hasIndexInBlock(bb, i, sv)
      )
    }

    override Stage0::Node getValue() { result = this.getImpl().getValue() }

    override predicate isCertain() { this.getImpl().isCertain() }

    override Operand getAddressOperand() { result = this.getImpl().getAddressOperand() }

    override int getIndirectionIndex() { result = this.getImpl().getIndirectionIndex() }

    override int getIndirection() { result = this.getImpl().getIndirection() }
  }

  class GlobalDef extends Def {
    GlobalDefImpl global;

    GlobalDef() { isGlobal(def, global) }

    /** Gets a textual representation of this definition. */
    override string toString() { result = global.toString() }

    final override Location getLocation() { result = global.getLocation() }

    /**
     * Gets the type of this definition after specifiers have been deeply stripped
     * and typedefs have been resolved.
     */
    DataFlowType getUnspecifiedType() { result = global.getUnspecifiedType() }

    /**
     * Gets the type of this definition, after typedefs have been resolved.
     */
    DataFlowType getUnderlyingType() { result = global.getUnderlyingType() }

    /** Gets the `IRFunction` whose body is evaluated after this definition. */
    IRFunction getIRFunction() { result = global.getIRFunction() }

    /** Gets the global variable associated with this definition. */
    GlobalLikeVariable getVariable() { result = global.getVariable() }

    override predicate isCertain() { any() }

    final override int getIndirectionIndex() { result = global.getIndirectionIndex() }

    final override int getIndirection() { result = global.getIndirection() }
  }

  class Phi extends TPhi, SsaDef {
    PhiNode phi;

    Phi() { this = TPhi(phi) }

    final override PhiNode asPhi() { result = phi }

    final override Location getLocation() { result = phi.getBasicBlock().getLocation() }

    override string toString() { result = phi.toString() }

    SsaPhiInputNode getNode(IRBlock block) {
      result.getPhiNode() = phi and result.getBlock() = block
    }

    predicate hasInputFromBlock(DefinitionExt inp, IRBlock bb) {
      inp = SsaCached::phiHasInputFromBlockExt(phi, bb)
    }

    final DefinitionExt getAnInput() { this.hasInputFromBlock(result, _) }
  }

  private module SsaImpl = SsaImplCommon::Make<Location, SsaInput>;

  /**
   * The final SSA predicates used for dataflow purposes.
   */
  cached
  module SsaCached {
    /**
     * Holds if `def` is accessed at index `i1` in basic block `bb1` (either a read
     * or a write), `def` is read at index `i2` in basic block `bb2`, and there is a
     * path between them without any read of `def`.
     */
    cached
    predicate adjacentDefReadExt(
      DefinitionExt def, SourceVariable sv, IRBlock bb1, int i1, IRBlock bb2, int i2
    ) {
      SsaImpl::adjacentDefReadExt(def, sv, bb1, i1, bb2, i2)
    }

    /**
     * Holds if the node at index `i` in `bb` is a last reference to SSA definition
     * `def`. The reference is last because it can reach another write `next`,
     * without passing through another read or write.
     *
     * The path from node `i` in `bb` to `next` goes via basic block `input`,
     * which is either a predecessor of the basic block of `next`, or `input` =
     * `bb` in case `next` occurs in basic block `bb`.
     */
    cached
    predicate lastRefRedefExt(
      DefinitionExt def, SourceVariable sv, IRBlock bb, int i, IRBlock input, DefinitionExt next
    ) {
      SsaImpl::lastRefRedefExt(def, sv, bb, i, input, next)
    }

    cached
    DefinitionExt phiHasInputFromBlockExt(PhiNode phi, IRBlock bb) {
      SsaImpl::phiHasInputFromBlockExt(phi, result, bb)
    }

    cached
    predicate ssaDefReachesReadExt(SourceVariable v, DefinitionExt def, IRBlock bb, int i) {
      SsaImpl::ssaDefReachesReadExt(v, def, bb, i)
    }

    predicate variableRead = SsaInput::variableRead/4;

    predicate variableWrite = SsaInput::variableWrite/4;
  }

  /**
   * An static single assignment (SSA) phi node.
   *
   * This is either a normal phi node or a phi-read node.
   */
  class PhiNode extends SsaImpl::DefinitionExt {
    PhiNode() {
      this instanceof SsaImpl::PhiNode or
      this instanceof SsaImpl::PhiReadNode
    }

    /**
     * Holds if this phi node is a phi-read node.
     *
     * Phi-read nodes are like normal phi nodes, but they are inserted based
     * on reads instead of writes.
     */
    predicate isPhiRead() { this instanceof SsaImpl::PhiReadNode }

    /**
     * Holds if the node at index `i` in `bb` is a last reference to SSA
     * definition `def` of `sv`. The reference is last because it can reach
     * this phi node, without passing through another read or write.
     *
     * The path from node `i` in `bb` to this phi node goes via basic block
     * `input`, which is either a predecessor of the basic block of this phi
     * node, or `input` = `bb` in case this phi node occurs in basic block `bb`.
     */
    predicate hasInputFromBlock(
      DefinitionExt def, SourceVariable sv, IRBlock bb, int i, IRBlock input
    ) {
      SsaCached::lastRefRedefExt(def, sv, bb, i, input, this)
    }

    /** Gets a definition that is an input to this phi node. */
    final DefinitionExt getAnInput() { this.hasInputFromBlock(result, _, _, _, _) }
  }

  /** An static single assignment (SSA) definition. */
  class DefinitionExt extends SsaImpl::DefinitionExt {
    private DefinitionExt getAPhiInputOrPriorDefinition() { result = this.(PhiNode).getAnInput() }

    /**
     * Gets a definition that ultimately defines this SSA definition and is
     * not itself a phi node.
     */
    final DefinitionExt getAnUltimateDefinition() {
      result = this.getAPhiInputOrPriorDefinition*() and
      not result instanceof PhiNode
    }

    /** Gets a node that represents a read of this SSA definition. */
    pragma[nomagic]
    Node getARead() {
      exists(SourceVariable sv, IRBlock bb, int i |
        SsaCached::ssaDefReachesReadExt(sv, this, bb, i)
      |
        useToNode(bb, i, sv, result)
        or
        phiToNode(result, sv, bb, i)
      )
    }
  }

  private newtype TNode =
    TNode1(Stage1::Node node) or
    TGlobalLikeVariableNode(GlobalLikeVariable var, int indirectionIndex) {
      indirectionIndex =
        [getMinIndirectionsForType(var.getUnspecifiedType()) .. Stage0Output::getMaxIndirectionsForType(var.getUnspecifiedType())]
    } or
    TSsaPhiInputNode(PhiNode phi, IRBlock input) { phi.hasInputFromBlock(_, _, _, _, input) } or
    TSsaPhiNode(PhiNode phi) or
    TFinalParameterNode(Parameter p, int indirectionIndex) {
      exists(FinalParameterUse use |
        use.getParameter() = p and
        use.getIndirectionIndex() = indirectionIndex
      )
    } or
    TFinalGlobalValue(GlobalUse globalUse) or
    TInitialGlobalValue(GlobalDef globalUse) or
    TArgumentOutNode(ArgumentOperand operand, int indirectionIndex) {
      isModifiableByCall(operand, indirectionIndex)
    } or
    TPostUpdateNodeImpl(Operand operand, int indirectionIndex) {
      operand = any(FieldAddress fa).getObjectAddressOperand() and
      indirectionIndex = [0 .. Stage0Output::countIndirectionsForCppType(getLanguageType(operand))]
    }

  abstract class Node extends TNode {
    abstract string toString();

    abstract Instruction asInstruction();

    abstract Operand asOperand();

    abstract Declaration getEnclosingCallable();

    abstract Declaration getFunction();

    abstract DataFlowType getType();

    abstract Location getLocation();

    abstract predicate isGLValue();

    abstract predicate hasIndexInBlock(IRBlock block, int i);

    abstract string stars();

    Operand asIndirectOperand(int indirectionIndex) {
      hasOperandAndIndex(this, result, indirectionIndex)
    }
  }

  private class Node1 extends Node, TNode1 {
    Stage1::Node n;

    Node1() { this = TNode1(n) }

    override string toString() { result = n.toString() }

    final override Instruction asInstruction() { result = n.asInstruction() }

    final override Operand asOperand() { result = n.asOperand() }

    final override Declaration getEnclosingCallable() { result = n.getEnclosingCallable() }

    final override Declaration getFunction() { result = n.getFunction() }

    final override DataFlowType getType() { result = n.getType() }

    final override Location getLocation() { result = n.getLocation() }

    final override predicate isGLValue() { n.isGLValue() }

    final override string stars() { result = n.stars() }

    final override predicate hasIndexInBlock(IRBlock block, int i) { n.hasIndexInBlock(block, i) }
  }

  pragma[nomagic]
  private predicate finalParameterNodeHasArgumentAndIndex(
    FinalParameterNode node, int argumentIndex, int indirectionIndex
  ) {
    node.getArgumentIndex() = argumentIndex and
    node.getIndirectionIndex() = indirectionIndex
  }

  /**
   * INTERNAL: do not use.
   *
   * A node representing the value of an update parameter
   * just before reaching the end of a function.
   */
  class FinalParameterNode extends Node, ReturnNodeImpl, TFinalParameterNode {
    Parameter p;
    int indirectionIndex;

    FinalParameterNode() { this = TFinalParameterNode(p, indirectionIndex) }

    final override Instruction asInstruction() { none() }

    final override Operand asOperand() { none() }

    /** Gets the parameter associated with this final use. */
    Parameter getParameter() { result = p }

    /** Gets the underlying indirection index. */
    int getIndirectionIndex() { result = indirectionIndex }

    /** Gets the argument index associated with this final use. */
    final int getArgumentIndex() { result = p.getIndex() }

    override Declaration getFunction() { result = p.getFunction() }

    override Declaration getEnclosingCallable() { result = this.getFunction() }

    override DataFlowType getType() {
      result = Stage0Output::getTypeImpl(p.getUnderlyingType(), indirectionIndex)
    }

    final override Location getLocation() {
      // Parameters can have multiple locations. When there's a unique location we use
      // that one, but if multiple locations exist we default to an unknown location.
      result = unique( | | p.getLocation())
      or
      not exists(unique( | | p.getLocation())) and
      result instanceof UnknownDefaultLocation
    }

    final override string stars() { result = repeatStars(indirectionIndex) }

    override string toString() { result = this.stars() + p.toString() }

    final override predicate isGLValue() { none() }

    final override predicate hasIndexInBlock(IRBlock block, int i) {
      none() // TODO
    }

    final override ReturnKind getKind() {
      exists(int argumentIndex |
        finalParameterNodeHasArgumentAndIndex(this, argumentIndex, indirectionIndex) and
        result = TArgReturnKind(argumentIndex, indirectionIndex)
      )
    }
  }

  /**
   * INTERNAL: Do not use.
   */
  class PostUpdateNodeImpl extends PostUpdateNode, TPostUpdateNodeImpl {
    int indirectionIndex;
    Operand operand;
    FieldAddress fieldAddress;

    PostUpdateNodeImpl() {
      this = TPostUpdateNodeImpl(operand, indirectionIndex) and
      operand = fieldAddress.getObjectAddressOperand()
    }

    FieldAddress getFieldAddress() { result = fieldAddress }

    Field getUpdatedField() { result = this.getFieldAddress().getField() }

    final override Instruction asInstruction() { none() }

    final override Operand asOperand() { none() }

    final override string stars() { result = repeatStars(indirectionIndex) }

    final override predicate isGLValue() { none() }

    final override predicate hasIndexInBlock(IRBlock block, int i) {
      this.getPreUpdateNode().hasIndexInBlock(block, i)
    }

    final override string toString() {
      result = this.getPreUpdateNode().toString() + " [post update]"
    }

    final override DataFlowType getType() { result = this.getPreUpdateNode().getType() }

    override Declaration getFunction() { result = this.getPreUpdateNode().getFunction() }

    override Declaration getEnclosingCallable() {
      result = this.getPreUpdateNode().getEnclosingCallable()
    }

    /** Gets the operand associated with this node. */
    Operand getOperand() { result = operand }

    /** Gets the indirection index associated with this node. */
    int getIndirectionIndex() { result = indirectionIndex }

    final override Location getLocation() { result = operand.getLocation() }

    final override Node getPreUpdateNode() {
      indirectionIndex > 0 and
      hasOperandAndIndex(result, operand, indirectionIndex)
      or
      indirectionIndex = 0 and
      result.asOperand() = operand
    }
  }

  /**
   * INTERNAL: Do not use.
   *
   * A node that is used as an input to a phi node.
   *
   * This class exists to allow more powerful barrier guards. Consider this
   * example:
   *
   * ```cpp
   * int x = source();
   * if(!safe(x)) {
   *   x = clear();
   * }
   * // phi node for x here
   * sink(x);
   * ```
   *
   * At the phi node for `x` it is neither the case that `x` is dominated by
   * `safe(x)`, or is the case that the phi is dominated by a clearing of `x`.
   *
   * By inserting a "phi input" node as the last entry in the basic block that
   * defines the inputs to the phi we can conclude that each of those inputs are
   * safe to pass to `sink`.
   */
  class SsaPhiInputNode extends Node, TSsaPhiInputNode {
    PhiNode phi;
    IRBlock block;

    SsaPhiInputNode() { this = TSsaPhiInputNode(phi, block) }

    /** Gets the phi node associated with this node. */
    PhiNode getPhiNode() { result = phi }

    /** Gets the basic block in which this input originates. */
    IRBlock getBlock() { result = block }

    final override Instruction asInstruction() { none() }

    final override Operand asOperand() { none() }

    final override string stars() { result = repeatStars(phi.getSourceVariable().getIndirection()) }

    final override predicate hasIndexInBlock(IRBlock block_, int index) {
      block = block_ and
      index = block.getInstructionCount()
    }

    override Declaration getEnclosingCallable() { result = this.getFunction() }

    override Declaration getFunction() { result = phi.getBasicBlock().getEnclosingFunction() }

    override DataFlowType getType() { result = this.getSourceVariable().getType() }

    override predicate isGLValue() { phi.getSourceVariable().isGLValue() }

    final override Location getLocation() { result = block.getLastInstruction().getLocation() }

    override string toString() { result = "Phi input" }

    /** Gets the source variable underlying this phi node. */
    SourceVariable getSourceVariable() { result = phi.getSourceVariable() }
  }

  SsaPhiInputNode ssaPhiInputNode(PhiNode phi, IRBlock block) {
    result = TSsaPhiInputNode(phi, block)
  }

  /**
   * INTERNAL: do not use.
   *
   * A phi node produced by the shared SSA library, viewed as a node in a data flow graph.
   */
  class SsaPhiNode extends Node, TSsaPhiNode {
    PhiNode phi;

    SsaPhiNode() { this = TSsaPhiNode(phi) }

    /** Gets the phi node associated with this node. */
    PhiNode getPhiNode() { result = phi }

    final override Instruction asInstruction() { none() }

    final override Operand asOperand() { none() }

    override Declaration getEnclosingCallable() { result = this.getFunction() }

    override Declaration getFunction() { result = phi.getBasicBlock().getEnclosingFunction() }

    override DataFlowType getType() {
      exists(SourceVariable sv |
        this.getPhiNode().definesAt(sv, _, _, _) and
        result = sv.getType()
      )
    }

    override predicate isGLValue() { phi.getSourceVariable().isGLValue() }

    final override Location getLocation() { result = phi.getBasicBlock().getLocation() }

    final override string stars() { result = repeatStars(phi.getSourceVariable().getIndirection()) } // TODO: Get rid of stars predicate?

    final override predicate hasIndexInBlock(IRBlock block, int index) {
      phi.definesAt(_, block, index, _)
    }

    override string toString() { result = phi.toString() }

    /**
     * Gets a node that is used as input to this phi node.
     * `fromBackEdge` is true if data flows along a back-edge,
     * and `false` otherwise.
     */
    cached
    final Node getAnInput(boolean fromBackEdge) {
      result.(SsaPhiInputNode).getPhiNode() = phi and
      exists(IRBlock bPhi, IRBlock bResult |
        bPhi = phi.getBasicBlock() and result.hasIndexInBlock(bResult, _)
      |
        if bPhi.dominates(bResult) then fromBackEdge = true else fromBackEdge = false
      )
    }

    /** Gets a node that is used as input to this phi node. */
    final Node getAnInput() { result = this.getAnInput(_) }

    /** Gets the source variable underlying this phi node. */
    SourceVariable getSourceVariable() { result = phi.getSourceVariable() }

    /**
     * Holds if this phi node is a phi-read node.
     *
     * Phi-read nodes are like normal phi nodes, but they are inserted based
     * on reads instead of writes.
     */
    predicate isPhiRead() { phi.isPhiRead() }
  }

  class OperandNode extends Node1 {
    override Stage1::OperandNode n;

    Operand getOperand() { result = n.getOperand() }
  }

  OperandNode operandNode(Operand operand) { result.getOperand() = operand }

  class InstructionNode extends Node1 {
    override Stage1::InstructionNode n;

    Instruction getInstruction() { result = n.getInstruction() }
  }

  InstructionNode instructionNode(Instruction instr) { result.getInstruction() = instr }

  class IndirectOperandNode extends Node1 {
    override Stage1::IndirectOperandNode n;

    predicate hasOperandAndIndirectionIndex(Operand operand, int indirectionIndex) {
      n.hasOperandAndIndirectionIndex(operand, indirectionIndex)
    }
  }

  class IndirectInstructionNode extends Node1 {
    override Stage1::IndirectInstructionNode n;

    predicate hasInstructionAndIndirectionIndex(Instruction instr, int indirectionIndex) {
      n.hasInstructionAndIndirectionIndex(instr, indirectionIndex)
    }
  }

  class DataFlowCallable = Stage1::DataFlowCallable;

  class DataFlowCall = Stage1::DataFlowCall;

  DataFlowCallable nodeGetEnclosingCallable(Node node) {
    exists(Stage1::Node n |
      node = TNode1(n) and
      result = Stage1::nodeGetEnclosingCallable(n)
    )
    or
    none() // TODO
  }

  class Position = Stage1::Position;

  class ArgumentNode extends Node1 {
    override Stage1::ArgumentNode n;

    predicate argumentOf(DataFlowCall call, Position pos) { n.argumentOf(call, pos) }
  }

  abstract class OutNode extends Node {
    DataFlowCall call;

    DataFlowCall getCall() { result = call }

    abstract ReturnKind getReturnKind();
  }

  private class Stage1OutNode extends OutNode, Node1 {
    override Stage1::OutNode n;

    Stage1OutNode() { call = n.getCall() }

    override ReturnKind getReturnKind() { result = TStage1ReturnKind(n.getReturnKind()) }
  }

  abstract class PostUpdateNode extends Node {
    abstract Node getPreUpdateNode();
  }

  class ArgumentOutNode extends PostUpdateNode, OutNode, TArgumentOutNode {
    ArgumentOperand operand;
    int indirectionIndex;

    ArgumentOutNode() { this = TArgumentOutNode(operand, indirectionIndex) }

    final override Node getPreUpdateNode() {
      indirectionIndex > 0 and
      hasOperandAndIndex(result, operand, indirectionIndex)
      or
      indirectionIndex = 0 and
      result.asOperand() = operand
    }

    int getArgumentIndex() {
      result = operand.(PositionalArgumentOperand).getIndex()
      or
      operand instanceof ThisArgumentOperand and
      result = -1
    }

    ArgumentOperand getOperand() { result = operand }

    int getIndirectionIndex() { result = indirectionIndex }

    CallInstruction getCallInstruction() { result = operand.getCall() }

    final override string toString() {
      exists(string prefix | if indirectionIndex > 0 then prefix = "" else prefix = "pointer to " |
        // This string should be unique enough to be helpful but common enough to
        // avoid storing too many different strings.
        result = prefix + this.getStaticCallTarget().getName() + " output argument"
        or
        not exists(this.getStaticCallTarget()) and
        result = prefix + "output argument"
      )
    }

    /**
     * Gets the `Function` that the call targets, if this is statically known.
     */
    Function getStaticCallTarget() { result = this.getCallInstruction().getStaticCallTarget() }

    final override Instruction asInstruction() { none() }

    final override Operand asOperand() { none() }

    final override Declaration getEnclosingCallable() { result = this.getFunction() }

    final override Declaration getFunction() { result = operand.getUse().getEnclosingFunction() }

    final override DataFlowType getType() { result = this.getPreUpdateNode().getType() }

    final override Location getLocation() { result = operand.getLocation() }

    final override predicate isGLValue() { none() }

    final override predicate hasIndexInBlock(IRBlock block, int i) {
      block.getInstruction(i) = operand.getUse()
    }

    final override string stars() { result = repeatStars(indirectionIndex) }

    final override ArgReturnKind getReturnKind() {
      result = TArgReturnKind(this.getArgumentIndex(), indirectionIndex)
    }
  }

  private class Stage1PostUpdateNode extends Node1, PostUpdateNode {
    override Stage1::PostUpdateNode n;

    final override Node getPreUpdateNode() { result = TNode1(n.getPreUpdateNode()) }

    final override string toString() { result = n.toString() }
  }

  private newtype TReturnKind =
    TStage1ReturnKind(Stage1::ReturnKind kind) or
    TArgReturnKind(int argumentIndex, int indirectionIndex) {
      // derive a possible return argument from SSA
      exists(FinalParameterUse use |
        use.getIndirectionIndex() = indirectionIndex and
        use.getArgumentIndex() = argumentIndex
      )
    }

  abstract class ReturnKind extends TReturnKind {
    abstract int getIndirectionIndex();

    /** Gets a textual representation of this return kind. */
    abstract string toString();
  }

  class Stage1ReturnKind extends ReturnKind, TStage1ReturnKind {
    Stage1::ReturnKind kind;

    Stage1ReturnKind() { this = TStage1ReturnKind(kind) }

    final override int getIndirectionIndex() { result = kind.getIndirectionIndex() }

    final override string toString() { result = kind.toString() }
  }

  class ArgReturnKind extends ReturnKind, TArgReturnKind {
    int argumentIndex;
    int indirectionIndex;

    ArgReturnKind() { this = TArgReturnKind(argumentIndex, indirectionIndex) }

    final override int getIndirectionIndex() { result = indirectionIndex }

    int getArgumentIndex() { result = argumentIndex }

    final override string toString() {
      result = repeatStars(indirectionIndex) + "outparam[" + argumentIndex.toString() + "]"
    }
  }

  abstract private class ReturnNodeImpl instanceof Node {
    abstract ReturnKind getKind();

    abstract string toString();
  }

  private class Stage1ReturNode extends ReturnNodeImpl, Node1 {
    override Stage1::ReturnNode n;

    final override ReturnKind getKind() { result = TStage1ReturnKind(n.getKind()) }

    final override string toString() { result = Node1.super.toString() }
  }

  final class ReturnNode = ReturnNodeImpl;

  predicate decodePosition = Stage1::decodePosition/1;

  predicate hasOperandAndIndex(IndirectOperandNode n, Operand op, int indirectionIndex) {
    n.hasOperandAndIndirectionIndex(op, indirectionIndex)
  }

  predicate hasInstructionAndIndex(
    IndirectInstructionNode n, Instruction instr, int indirectionIndex
  ) {
    n.hasInstructionAndIndirectionIndex(instr, indirectionIndex)
  }

  predicate nodeHasOperand(Node node, Operand operand, int indirectionIndex) {
    node.asOperand() = operand and indirectionIndex = 0
    or
    hasOperandAndIndex(node, operand, indirectionIndex)
  }

  predicate nodeHasInstruction(Node node, Instruction instr, int indirectionIndex) {
    node.asInstruction() = instr and indirectionIndex = 0
    or
    hasInstructionAndIndex(node, instr, indirectionIndex)
  }

  predicate localFlowStep(Node nodeFrom, Node nodeTo) {
    exists(Stage1::Node nFrom, Stage1::Node nTo |
      nodeFrom = TNode1(nFrom) and
      nodeTo = TNode1(nTo) and
      Stage1::localFlowStep(nFrom, nTo)
    )
    or
    postUpdateFlow(nodeFrom, nodeTo)
    or
    ssaFlow(nodeFrom, nodeTo)
    or
    nodeFrom.(SsaPhiInputNode).getPhiNode() = nodeTo.(SsaPhiNode).getPhiNode()
    or
    fromPhiNode(nodeFrom, nodeTo)
  }

  bindingset[f]
  pragma[inline_late]
  private int getFieldSize(Field f) { result = f.getType().getSize() }

  /**
   * Gets a field in the union `u` whose size
   * is `bytes` number of bytes.
   */
  private Field getAFieldWithSize(Cpp::Union u, int bytes) {
    result = u.getAField() and
    bytes = getFieldSize(result)
  }

  /**
   * Gets the maximum number of indirections to use for `ElementContent`.
   *
   * This should be equal to the largest number of stars (i.e., `*`s) in any
   * `Element` content across all of our MaD summaries, sources, and sinks.
   */
  int getMaxElementContentIndirectionIndex() { result = 5 }

  cached
  private newtype TContent =
    TFieldContent(Field f, int indirectionIndex) {
      // the indirection index for field content starts at 1 (because `TFieldContent` is thought of as
      // the address of the field, `FieldAddress` in the IR).
      indirectionIndex = [1 .. Stage0Output::getMaxIndirectionsForType(f.getUnspecifiedType())] and
      // Reads and writes of union fields are tracked using `UnionContent`.
      not f.getDeclaringType() instanceof Cpp::Union
    } or
    TUnionContent(Cpp::Union u, int bytes, int indirectionIndex) {
      exists(Field f |
        f = u.getAField() and
        bytes = getFieldSize(f) and
        // We key `UnionContent` by the union instead of its fields since a write to one
        // field can be read by any read of the union's fields. Again, the indirection index
        // is 1-based (because 0 is considered the address).
        indirectionIndex =
          [1 .. max(Stage0Output::getMaxIndirectionsForType(getAFieldWithSize(u, bytes)
                      .getUnspecifiedType())
            )]
      )
    } or
    TElementContent(int indirectionIndex) {
      indirectionIndex = [1 .. getMaxElementContentIndirectionIndex()]
    }

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

    /** Gets the indirection index of this `Content`. */
    abstract int getIndirectionIndex();

    /**
     * INTERNAL: Do not use.
     *
     * Holds if a write to this `Content` implies that `c` is
     * also cleared.
     *
     * For example, a write to a field `f` implies that any content of
     * the form `*f` is also cleared.
     */
    abstract predicate impliesClearOf(Content c);
  }

  /**
   * Gets the number of stars (i.e., `*`s) needed to produce the `toString`
   * output for `c`.
   */
  private string contentStars(Content c) { result = repeatStars(c.getIndirectionIndex() - 1) }

  /** A reference through a non-union instance field. */
  class FieldContent extends Content, TFieldContent {
    private Field f;
    private int indirectionIndex;

    FieldContent() { this = TFieldContent(f, indirectionIndex) }

    override string toString() { result = contentStars(this) + f.toString() }

    Field getField() { result = f }

    /** Gets the indirection index of this `FieldContent`. */
    pragma[inline]
    override int getIndirectionIndex() {
      pragma[only_bind_into](result) = pragma[only_bind_out](indirectionIndex)
    }

    override predicate impliesClearOf(Content c) {
      exists(FieldContent fc |
        fc = c and
        fc.getField() = f and
        // If `this` is `f` then `c` is cleared if it's of the
        // form `*f`, `**f`, etc.
        fc.getIndirectionIndex() >= indirectionIndex
      )
    }
  }

  /** A reference through an instance field of a union. */
  class UnionContent extends Content, TUnionContent {
    private Cpp::Union u;
    private int indirectionIndex;
    private int bytes;

    UnionContent() { this = TUnionContent(u, bytes, indirectionIndex) }

    override string toString() { result = contentStars(this) + u.toString() }

    /** Gets a field of the underlying union of this `UnionContent`, if any. */
    Field getAField() { result = u.getAField() and getFieldSize(result) = bytes }

    /** Gets the underlying union of this `UnionContent`. */
    Cpp::Union getUnion() { result = u }

    /** Gets the indirection index of this `UnionContent`. */
    pragma[inline]
    override int getIndirectionIndex() {
      pragma[only_bind_into](result) = pragma[only_bind_out](indirectionIndex)
    }

    override predicate impliesClearOf(Content c) {
      exists(UnionContent uc |
        uc = c and
        uc.getUnion() = u and
        // If `this` is `u` then `c` is cleared if it's of the
        // form `*u`, `**u`, etc. (and we ignore `bytes` because
        // we know the entire union is overwritten because it's a
        // union).
        uc.getIndirectionIndex() >= indirectionIndex
      )
    }
  }

  /**
   * A `Content` that represents one of the elements of a
   * container (e.g., `std::vector`).
   */
  class ElementContent extends Content, TElementContent {
    int indirectionIndex;

    ElementContent() { this = TElementContent(indirectionIndex) }

    pragma[inline]
    override int getIndirectionIndex() {
      pragma[only_bind_into](result) = pragma[only_bind_out](indirectionIndex)
    }

    override predicate impliesClearOf(Content c) { none() }

    override string toString() { result = contentStars(this) + "element" }
  }

  /**
   * Holds if `operandFrom` flows to `operandTo` using a sequence of conversion-like
   * operations and exactly `n` `LoadInstruction` operations.
   */
  private predicate numberOfLoadsFromOperandRec(
    Operand operandFrom, Operand operandTo, int ind, boolean certain
  ) {
    exists(Instruction load | Stage0Output::isDereference(load, operandFrom, _) |
      operandTo = operandFrom and ind = 0 and certain = true
      or
      numberOfLoadsFromOperand(load.getAUse(), operandTo, ind - 1, certain)
    )
    or
    exists(Operand op, Instruction instr, boolean isPointerArith, boolean certain0 |
      instr = op.getDef() and
      conversionFlow(operandFrom, instr, isPointerArith, _) and
      numberOfLoadsFromOperand(op, operandTo, ind, certain0)
    |
      if isPointerArith = true then certain = false else certain = certain0
    )
  }

  /**
   * Holds if `operandFrom` flows to `operandTo` using a sequence of conversion-like
   * operations and exactly `n` `LoadInstruction` operations.
   */
  private predicate numberOfLoadsFromOperand(
    Operand operandFrom, Operand operandTo, int n, boolean certain
  ) {
    numberOfLoadsFromOperandRec(operandFrom, operandTo, n, certain)
    or
    not Stage0Output::isDereference(_, operandFrom, _) and
    not conversionFlow(operandFrom, _, _, _) and
    operandFrom = operandTo and
    n = 0 and
    certain = true
  }

  predicate storeStep(Node node1, Content c, Node node2, boolean certain) {
    exists(
      PostUpdateNodeImpl postFieldUpdate, int indirectionIndex1, int numberOfLoads,
      StoreInstruction store
    |
      postFieldUpdate = node2 and
      nodeHasInstruction(node1, store, pragma[only_bind_into](indirectionIndex1)) and
      postFieldUpdate.getIndirectionIndex() = 1 and
      numberOfLoadsFromOperand(postFieldUpdate.getFieldAddress(),
        store.getDestinationAddressOperand(), numberOfLoads, certain)
    |
      exists(FieldContent fc | fc = c |
        fc.getField() = postFieldUpdate.getUpdatedField() and
        fc.getIndirectionIndex() = 1 + indirectionIndex1 + numberOfLoads
      )
      or
      exists(UnionContent uc | uc = c |
        uc.getAField() = postFieldUpdate.getUpdatedField() and
        uc.getIndirectionIndex() = 1 + indirectionIndex1 + numberOfLoads
      )
    )
  }

  predicate readStep(Node node1, Content c, Node node2) {
    exists(FieldAddress fa1, Operand operand, int numberOfLoads, int indirectionIndex2 |
      nodeHasOperand(node2, operand, indirectionIndex2) and
      // The `1` here matches the `node2.getIndirectionIndex() = 1` conjunct
      // in `storeStep`.
      nodeHasOperand(node1, fa1.getObjectAddressOperand(), 1) and
      numberOfLoadsFromOperand(fa1, operand, numberOfLoads, _)
    |
      exists(FieldContent fc | fc = c |
        fc.getField() = fa1.getField() and
        fc.getIndirectionIndex() = indirectionIndex2 + numberOfLoads
      )
      or
      exists(UnionContent uc | uc = c |
        uc.getAField() = fa1.getField() and
        uc.getIndirectionIndex() = indirectionIndex2 + numberOfLoads
      )
    )
  }
}
