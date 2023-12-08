private import semmle.code.cpp.ir.implementation.internal.TInstruction
private import IRFunctionImports::IRFunctionBase
private import IRInternal
private import SplitImports as Imports
private import Imports::Opcode
private import Imports::OperandTag
private import Imports::Overlap
private import Imports::TInstruction
private import Imports::RawIR as RawIR
private import semmle.code.cpp.ir.implementation.split_raw.IR
private import semmle.code.cpp.ir.implementation.raw.internal.IRConstruction as IRConstruction

class TStageInstruction = TRawInstruction;

IRConstruction::StageInstruction unsplit(TStageInstruction i) {
  exists(IRConstruction::Node n |
    i = TRawInstruction(n) and
    result = n.getAstNode()
  )
}

predicate hasInstruction(TStageInstruction i) { IRConstruction::hasInstruction(unsplit(i)) }

cached
predicate instructionHasSortKeys(Instruction instr, int key1, int key2, string key3) {
  instr.getSplit().toString() = key3 and
  IRConstruction::instructionHasSortKeys(unsplit(instr), key1, key2, _)
}

cached
string getInstructionUniqueId(Instruction instr) {
  result = IRConstruction::getInstructionUniqueId(unsplit(instr))
}

cached
IRFunctionBase getInstructionEnclosingIRFunction(Instruction instr) {
  result = IRConstruction::getInstructionEnclosingIRFunction(unsplit(instr))
}

cached
Language::AST getInstructionAst(Instruction instr) {
  result = IRConstruction::getInstructionAst(unsplit(instr))
}

cached
Language::Expr getInstructionConvertedResultExpression(Instruction instruction) {
  result = IRConstruction::getInstructionConvertedResultExpression(unsplit(instruction))
}

cached
Language::Expr getInstructionUnconvertedResultExpression(Instruction instruction) {
  result = IRConstruction::getInstructionUnconvertedResultExpression(unsplit(instruction))
}

cached
Language::CppType getInstructionExceptionType(Instruction instruction) {
  result = IRConstruction::getInstructionExceptionType(unsplit(instruction))
}

cached
IRVariable getInstructionVariable(Instruction instruction) {
  result = IRConstruction::getInstructionVariable(unsplit(instruction))
}

cached
Language::Field getInstructionField(Instruction instruction) {
  result = IRConstruction::getInstructionField(unsplit(instruction))
}

cached
Language::Function getInstructionFunction(Instruction instruction) {
  result = IRConstruction::getInstructionFunction(unsplit(instruction))
}

cached
string getInstructionConstantValue(Instruction instruction) {
  result = IRConstruction::getInstructionConstantValue(unsplit(instruction))
}

cached
int getInstructionIndex(Instruction instruction) {
  result = IRConstruction::getInstructionIndex(unsplit(instruction))
}

cached
int getInstructionElementSize(Instruction instruction) {
  result = IRConstruction::getInstructionElementSize(unsplit(instruction))
}

cached
predicate getInstructionInheritance(
  Instruction instruction, Language::Class baseClass, Language::Class derivedClass
) {
  IRConstruction::getInstructionInheritance(unsplit(instruction), baseClass, derivedClass)
}

cached
Language::BuiltInOperation getInstructionBuiltInOperation(Instruction instruction) {
  result = IRConstruction::getInstructionBuiltInOperation(unsplit(instruction))
}

cached
Language::LanguageType getInstructionResultType(Instruction instr) {
  result = IRConstruction::getInstructionResultType(unsplit(instr))
}

cached
predicate getInstructionOpcode(Opcode opcode, Instruction instr) {
  IRConstruction::getInstructionOpcode(opcode, unsplit(instr))
}

cached
predicate hasModeledMemoryResult(Instruction instruction) {
  IRConstruction::hasModeledMemoryResult(unsplit(instruction))
}

cached
predicate hasConflatedMemoryResult(Instruction instruction) {
  IRConstruction::hasConflatedMemoryResult(unsplit(instruction))
}

cached
Instruction getInstructionSuccessor(Instruction instruction, EdgeKind kind) {
  exists(IRConstruction::Node pred, IRConstruction::Node succ |
    instruction = TRawInstruction(pred) and
    result = TRawInstruction(succ) and
    succ = IRConstruction::getASuccessor(pred, kind)
  )
}

cached
Instruction getPrimaryInstructionForSideEffect(Instruction instruction) {
  unsplit(result) = IRConstruction::getPrimaryInstructionForSideEffect(unsplit(instruction)) // TODO: This conflates splits
}

cached
predicate getIntervalUpdatedByChi(ChiInstruction chi, int startBitOffset, int endBitOffset) {
  IRConstruction::getIntervalUpdatedByChi(unsplit(chi), startBitOffset, endBitOffset)
}

cached
predicate chiOnlyPartiallyUpdatesLocation(ChiInstruction chi) {
  IRConstruction::chiOnlyPartiallyUpdatesLocation(unsplit(chi))
}

cached
Instruction getPhiInstructionBlockStart(PhiInstruction instr) { none() }

cached
Instruction getInstructionBackEdgeSuccessor(Instruction instruction, EdgeKind kind) {
  // TODO
  none()
}

predicate getTempVariableUniqueId = IRConstruction::getTempVariableUniqueId/1;

Instruction getMemoryOperandDefinition(
  Instruction instruction, MemoryOperandTag tag, Overlap overlap
) {
  unsplit(result) = IRConstruction::getMemoryOperandDefinition(unsplit(instruction), tag, overlap)
}

cached
predicate isInCycle(Instruction instr) { none() }

cached
predicate getUsedInterval(NonPhiMemoryOperand operand, int startBitOffset, int endBitOffset) {
  none()
}

cached
Language::LanguageType getInstructionOperandType(Instruction instr, TypedOperandTag tag) {
  result = IRConstruction::getInstructionOperandType(unsplit(instr), tag)
}
