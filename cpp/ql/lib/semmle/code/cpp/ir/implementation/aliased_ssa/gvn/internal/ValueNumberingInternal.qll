private import ValueNumberingImports

pragma[nomagic]
private predicate nonUnique(Instruction instr) {
  variableAddressValueNumber(instr, _, _)
  or
  initializeParameterValueNumber(instr, _, _)
  or
  constantValueNumber(instr, _, _, _)
  or
  stringConstantValueNumber(instr, _, _, _)
  or
  exists(Instruction objectAddress |
    fieldAddressValueNumber0(instr, objectAddress, _, _) and
    nonUnique(objectAddress)
  )
  or
  exists(Instruction left, Instruction right |
    binaryValueNumber0(instr, left, right, _, _) and
    nonUnique(left) and
    nonUnique(right)
  )
  or
  exists(Instruction left, Instruction right |
    pointerArithmeticValueNumber0(instr, left, right, _, _, _) and
    nonUnique(left) and
    nonUnique(right)
  )
  or
  exists(Instruction unary |
    unaryValueNumber0(instr, unary, _, _) and
    nonUnique(unary)
  )
  or
  exists(Instruction unary |
    inheritanceConversionValueNumber0(instr, unary, _, _, _, _) and
    nonUnique(unary)
  )
  or
  exists(Instruction address, Instruction value |
    loadTotalOverlapValueNumber0(instr, address, value, _, _) and
    nonUnique(address) and
    nonUnique(value)
  )
  or
  nonUnique(instr.(CongruentCopyInstruction).getSourceValue())
}

newtype TValueNumber =
  TVariableAddressValueNumber(IRFunction irFunc, Language::AST ast) {
    variableAddressValueNumber(_, irFunc, ast)
  } or
  TInitializeParameterValueNumber(IRFunction irFunc, Language::AST var) {
    initializeParameterValueNumber(_, irFunc, var)
  } or
  TConstantValueNumber(IRFunction irFunc, IRType type, string value) {
    constantValueNumber(_, irFunc, type, value)
  } or
  TStringConstantValueNumber(IRFunction irFunc, IRType type, string value) {
    stringConstantValueNumber(_, irFunc, type, value)
  } or
  TFieldAddressValueNumber(IRFunction irFunc, Language::Field field, TValueNumber objectAddress) {
    exists(Instruction i |
      nonUnique(i) and
      fieldAddressValueNumber(i, irFunc, field, objectAddress)
    )
  } or
  TBinaryValueNumber(
    IRFunction irFunc, Opcode opcode, TValueNumber leftOperand, TValueNumber rightOperand
  ) {
    exists(Instruction i |
      nonUnique(i) and
      binaryValueNumber(i, irFunc, opcode, leftOperand, rightOperand)
    )
  } or
  TPointerArithmeticValueNumber(
    IRFunction irFunc, Opcode opcode, int elementSize, TValueNumber leftOperand,
    TValueNumber rightOperand
  ) {
    exists(Instruction i |
      nonUnique(i) and
      pointerArithmeticValueNumber(i, irFunc, opcode, elementSize, leftOperand, rightOperand)
    )
  } or
  TUnaryValueNumber(IRFunction irFunc, Opcode opcode, TValueNumber operand) {
    exists(Instruction i |
      nonUnique(i) and
      unaryValueNumber(i, irFunc, opcode, operand)
    )
  } or
  TInheritanceConversionValueNumber(
    IRFunction irFunc, Opcode opcode, Language::Class baseClass, Language::Class derivedClass,
    TValueNumber operand
  ) {
    exists(Instruction i |
      nonUnique(i) and
      inheritanceConversionValueNumber(i, irFunc, opcode, baseClass, derivedClass, operand)
    )
  } or
  TLoadTotalOverlapValueNumber(
    IRFunction irFunc, IRType type, TValueNumber memOperand, TValueNumber operand
  ) {
    exists(Instruction i |
      nonUnique(i) and
      loadTotalOverlapValueNumber(i, irFunc, type, memOperand, operand)
    )
  } or
  TUniqueValueNumber(IRFunction irFunc, Instruction instr) { uniqueValueNumber(instr, irFunc) }

/**
 * A `CopyInstruction` whose source operand's value is congruent to the definition of that source
 * operand.
 * For example:
 * ```
 * Point p = { 1, 2 };
 * Point q = p;
 * int a = p.x;
 * ```
 * The use of `p` on line 2 is linked to the definition of `p` on line 1, and is congruent to that
 * definition because it accesses the exact same memory.
 * The use of `p.x` on line 3 is linked to the definition of `p` on line 1 as well, but is not
 * congruent to that definition because `p.x` accesses only a subset of the memory defined by `p`.
 */
class CongruentCopyInstruction extends CopyInstruction {
  CongruentCopyInstruction() {
    this.getSourceValueOperand().getDefinitionOverlap() instanceof MustExactlyOverlap
  }
}

class LoadTotalOverlapInstruction extends LoadInstruction {
  LoadTotalOverlapInstruction() {
    this.getSourceValueOperand().getDefinitionOverlap() instanceof MustTotallyOverlap
  }
}

/**
 * Holds if this library knows how to assign a value number to the specified instruction, other than
 * a `unique` value number that is never shared by multiple instructions.
 */
private predicate numberableInstruction(Instruction instr) { nonUnique(instr) }

private predicate filteredNumberableInstruction(Instruction instr) {
  // count rather than strictcount to handle missing AST elements
  // separate instanceof and inline casts to avoid failed casts with a count of 0
  instr instanceof VariableAddressInstruction and
  count(instr.(VariableAddressInstruction).getIRVariable().getAst()) != 1
  or
  instr instanceof ConstantInstruction and
  count(instr.getResultIRType()) != 1
  or
  instr instanceof FieldAddressInstruction and
  count(instr.(FieldAddressInstruction).getField()) != 1
  or
  instr instanceof InheritanceConversionInstruction and
  (
    count(instr.(InheritanceConversionInstruction).getBaseClass()) != 1 or
    count(instr.(InheritanceConversionInstruction).getDerivedClass()) != 1
  )
}

private predicate variableAddressValueNumber(
  VariableAddressInstruction instr, IRFunction irFunc, Language::AST ast
) {
  instr.getEnclosingIRFunction() = irFunc and
  // The underlying AST element is used as value-numbering key instead of the
  // `IRVariable` to work around a problem where a variable or expression with
  // multiple types gives rise to multiple `IRVariable`s.
  unique( | | instr.getIRVariable().getAst()) = ast
}

private predicate initializeParameterValueNumber(
  InitializeParameterInstruction instr, IRFunction irFunc, Language::AST var
) {
  instr.getEnclosingIRFunction() = irFunc and
  // The underlying AST element is used as value-numbering key instead of the
  // `IRVariable` to work around a problem where a variable or expression with
  // multiple types gives rise to multiple `IRVariable`s.
  instr.getIRVariable().getAst() = var
}

private predicate constantValueNumber(
  ConstantInstruction instr, IRFunction irFunc, IRType type, string value
) {
  instr.getEnclosingIRFunction() = irFunc and
  unique( | | instr.getResultIRType()) = type and
  instr.getValue() = value
}

private predicate stringConstantValueNumber(
  StringConstantInstruction instr, IRFunction irFunc, IRType type, string value
) {
  instr.getEnclosingIRFunction() = irFunc and
  instr.getResultIRType() = type and
  instr.getValue().getValue() = value
}

private predicate fieldAddressValueNumber0(
  FieldAddressInstruction instr, Instruction objectAddress, IRFunction irFunc, Language::Field field
) {
  instr.getEnclosingIRFunction() = irFunc and
  unique( | | instr.getField()) = field and
  objectAddress = instr.getObjectAddress()
}

private predicate fieldAddressValueNumber(
  FieldAddressInstruction instr, IRFunction irFunc, Language::Field field,
  TValueNumber objectAddress
) {
  exists(Instruction objectAddressInstr |
    fieldAddressValueNumber0(instr, objectAddressInstr, irFunc, field) and
    tvalueNumber(objectAddressInstr) = objectAddress
  )
}

pragma[nomagic]
private predicate binaryValueNumber0(
  BinaryInstruction instr, Instruction left, Instruction right, IRFunction irFunc, Opcode opcode
) {
  not instr instanceof PointerArithmeticInstruction and
  instr.getEnclosingIRFunction() = irFunc and
  instr.getOpcode() = opcode and
  instr.getLeft() = left and
  instr.getRight() = right
}

pragma[nomagic]
private predicate binaryValueNumberLeft(
  BinaryInstruction instr, IRFunction irFunc, Opcode opcode, TValueNumber valueNumber
) {
  exists(Instruction left |
    binaryValueNumber0(instr, left, _, irFunc, opcode) and
    tvalueNumber(left) = valueNumber
  )
}

pragma[nomagic]
private predicate binaryValueNumberRight(
  BinaryInstruction instr, IRFunction irFunc, Opcode opcode, TValueNumber valueNumber
) {
  exists(Instruction right |
    binaryValueNumber0(instr, _, right, irFunc, opcode) and
    tvalueNumber(right) = valueNumber
  )
}

private predicate binaryValueNumber(
  BinaryInstruction instr, IRFunction irFunc, Opcode opcode, TValueNumber leftOperand,
  TValueNumber rightOperand
) {
  binaryValueNumberLeft(instr, irFunc, opcode, leftOperand) and
  binaryValueNumberRight(instr, irFunc, opcode, rightOperand)
}

pragma[nomagic]
private predicate pointerArithmeticValueNumber0(
  PointerArithmeticInstruction instr, Instruction left, Instruction right, IRFunction irFunc,
  Opcode opcode, int elementSize
) {
  instr.getEnclosingIRFunction() = irFunc and
  instr.getOpcode() = opcode and
  instr.getElementSize() = elementSize and
  instr.getLeft() = left and
  instr.getRight() = right
}

pragma[nomagic]
private predicate pointerArithmeticValueNumberLeft(
  PointerArithmeticInstruction instr, IRFunction irFunc, Opcode opcode, int elementSize,
  TValueNumber valueNumber
) {
  exists(Instruction left |
    pointerArithmeticValueNumber0(instr, left, _, irFunc, opcode, elementSize) and
    tvalueNumber(left) = valueNumber
  )
}

pragma[nomagic]
private predicate pointerArithmeticValueNumberRight(
  PointerArithmeticInstruction instr, IRFunction irFunc, Opcode opcode, int elementSize,
  TValueNumber valueNumber
) {
  exists(Instruction right |
    pointerArithmeticValueNumber0(instr, _, right, irFunc, opcode, elementSize) and
    tvalueNumber(right) = valueNumber
  )
}

private predicate pointerArithmeticValueNumber(
  PointerArithmeticInstruction instr, IRFunction irFunc, Opcode opcode, int elementSize,
  TValueNumber leftOperand, TValueNumber rightOperand
) {
  pointerArithmeticValueNumberLeft(instr, irFunc, opcode, elementSize, leftOperand) and
  pointerArithmeticValueNumberRight(instr, irFunc, opcode, elementSize, rightOperand)
}

private predicate unaryValueNumber0(
  UnaryInstruction instr, Instruction unary, IRFunction irFunc, Opcode opcode
) {
  instr.getEnclosingIRFunction() = irFunc and
  not instr instanceof InheritanceConversionInstruction and
  not instr instanceof CopyInstruction and
  not instr instanceof FieldAddressInstruction and
  instr.getOpcode() = opcode and
  instr.getUnary() = unary
}

private predicate unaryValueNumber(
  UnaryInstruction instr, IRFunction irFunc, Opcode opcode, TValueNumber operand
) {
  exists(Instruction unary |
    unaryValueNumber0(instr, unary, irFunc, opcode) and
    tvalueNumber(unary) = operand
  )
}

private predicate inheritanceConversionValueNumber0(
  InheritanceConversionInstruction instr, Instruction unary, IRFunction irFunc, Opcode opcode,
  Language::Class baseClass, Language::Class derivedClass
) {
  instr.getEnclosingIRFunction() = irFunc and
  instr.getOpcode() = opcode and
  instr.getUnary() = unary and
  unique( | | instr.getBaseClass()) = baseClass and
  unique( | | instr.getDerivedClass()) = derivedClass
}

private predicate inheritanceConversionValueNumber(
  InheritanceConversionInstruction instr, IRFunction irFunc, Opcode opcode,
  Language::Class baseClass, Language::Class derivedClass, TValueNumber operand
) {
  exists(Instruction unary |
    inheritanceConversionValueNumber0(instr, unary, irFunc, opcode, baseClass, derivedClass) and
    tvalueNumber(unary) = operand
  )
}

pragma[nomagic]
private predicate loadTotalOverlapValueNumber0(
  LoadTotalOverlapInstruction instr, Instruction address, Instruction value, IRFunction irFunc,
  IRType type
) {
  instr.getEnclosingIRFunction() = irFunc and
  instr.getResultIRType() = type and
  instr.getSourceAddress() = address and
  instr.getSourceValueOperand().getAnyDef() = value
}

pragma[nomagic]
private predicate loadTotalOverlapValueNumberAddress(
  LoadTotalOverlapInstruction instr, IRFunction irFunc, IRType type, TValueNumber valueNumber
) {
  exists(Instruction address |
    loadTotalOverlapValueNumber0(instr, address, _, irFunc, type) and
    tvalueNumber(address) = valueNumber
  )
}

pragma[nomagic]
private predicate loadTotalOverlapValueNumberValue(
  LoadTotalOverlapInstruction instr, IRFunction irFunc, IRType type, TValueNumber valueNumber
) {
  exists(Instruction value |
    loadTotalOverlapValueNumber0(instr, _, value, irFunc, type) and
    tvalueNumber(value) = valueNumber
  )
}

private predicate loadTotalOverlapValueNumber(
  LoadTotalOverlapInstruction instr, IRFunction irFunc, IRType type, TValueNumber memOperand,
  TValueNumber operand
) {
  loadTotalOverlapValueNumberAddress(instr, irFunc, type, operand) and
  loadTotalOverlapValueNumberValue(instr, irFunc, type, memOperand)
}

/**
 * Holds if `instr` should be assigned a unique value number because this library does not know how
 * to determine if two instances of that instruction are equivalent.
 */
private predicate uniqueValueNumber(Instruction instr, IRFunction irFunc) {
  instr.getEnclosingIRFunction() = irFunc and
  not instr.getResultIRType() instanceof IRVoidType and
  (
    not numberableInstruction(instr)
    or
    filteredNumberableInstruction(instr)
  )
}

/**
 * Gets the value number assigned to `instr`, if any. Returns at most one result.
 */
cached
TValueNumber tvalueNumber(Instruction instr) {
  result = nonUniqueValueNumber(instr)
  or
  exists(IRFunction irFunc |
    uniqueValueNumber(instr, irFunc) and
    result = TUniqueValueNumber(irFunc, instr)
  )
}

/**
 * Gets the value number assigned to the exact definition of `op`, if any.
 * Returns at most one result.
 */
TValueNumber tvalueNumberOfOperand(Operand op) { result = tvalueNumber(op.getDef()) }

/**
 * Gets the value number assigned to `instr`, if any, unless that instruction is assigned a unique
 * value number.
 */
private TValueNumber nonUniqueValueNumber(Instruction instr) {
  exists(IRFunction irFunc |
    irFunc = instr.getEnclosingIRFunction() and
    (
      exists(Language::AST ast |
        variableAddressValueNumber(instr, irFunc, ast) and
        result = TVariableAddressValueNumber(irFunc, ast)
      )
      or
      exists(Language::AST var |
        initializeParameterValueNumber(instr, irFunc, var) and
        result = TInitializeParameterValueNumber(irFunc, var)
      )
      or
      exists(string value, IRType type |
        constantValueNumber(instr, irFunc, type, value) and
        result = TConstantValueNumber(irFunc, type, value)
      )
      or
      exists(IRType type, string value |
        stringConstantValueNumber(instr, irFunc, type, value) and
        result = TStringConstantValueNumber(irFunc, type, value)
      )
      or
      exists(Language::Field field, TValueNumber objectAddress |
        fieldAddressValueNumber(instr, irFunc, field, objectAddress) and
        result = TFieldAddressValueNumber(irFunc, field, objectAddress)
      )
      or
      exists(Opcode opcode, TValueNumber leftOperand, TValueNumber rightOperand |
        binaryValueNumber(instr, irFunc, opcode, leftOperand, rightOperand) and
        result = TBinaryValueNumber(irFunc, opcode, leftOperand, rightOperand)
      )
      or
      exists(Opcode opcode, TValueNumber operand |
        unaryValueNumber(instr, irFunc, opcode, operand) and
        result = TUnaryValueNumber(irFunc, opcode, operand)
      )
      or
      exists(
        Opcode opcode, Language::Class baseClass, Language::Class derivedClass, TValueNumber operand
      |
        inheritanceConversionValueNumber(instr, irFunc, opcode, baseClass, derivedClass, operand) and
        result = TInheritanceConversionValueNumber(irFunc, opcode, baseClass, derivedClass, operand)
      )
      or
      exists(Opcode opcode, int elementSize, TValueNumber leftOperand, TValueNumber rightOperand |
        pointerArithmeticValueNumber(instr, irFunc, opcode, elementSize, leftOperand, rightOperand) and
        result =
          TPointerArithmeticValueNumber(irFunc, opcode, elementSize, leftOperand, rightOperand)
      )
      or
      exists(IRType type, TValueNumber memOperand, TValueNumber operand |
        loadTotalOverlapValueNumber(instr, irFunc, type, memOperand, operand) and
        result = TLoadTotalOverlapValueNumber(irFunc, type, memOperand, operand)
      )
      or
      // The value number of a copy is just the value number of its source value.
      result = tvalueNumber(instr.(CongruentCopyInstruction).getSourceValue())
    )
  )
}
