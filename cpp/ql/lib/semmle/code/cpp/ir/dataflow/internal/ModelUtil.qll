/**
 * Provides predicates for mapping the `FunctionInput` and `FunctionOutput`
 * classes used in function models to the corresponding instructions.
 */

private import semmle.code.cpp.ir.IR
private import semmle.code.cpp.ir.dataflow.DataFlow
private import DataFlowUtil
private import DataFlowPrivate

/**
 * Gets the instruction that goes into `input` for `call`.
 */
DataFlow::Node callInput(CallInstruction call, FunctionInput input) {
  result = TStageNode(FinalStage::callInput(call, input))
}

/**
 * Gets the instruction that holds the `output` for `call`.
 */
Node callOutput(CallInstruction call, FunctionOutput output) {
  result = TStageNode(FinalStage::callOutput(call, output, _))
}

DataFlow::Node callInput(CallInstruction call, FunctionInput input, int d) {
  exists(DataFlow::Node n | n = callInput(call, input) and d > 0 |
    // An argument or qualifier
    hasOperandAndIndex(result, n.asOperand(), d)
    or
    exists(Operand operand, int indirectionIndex |
      // A value pointed to by an argument or qualifier
      hasOperandAndIndex(n, operand, indirectionIndex) and
      hasOperandAndIndex(result, operand, indirectionIndex + d)
    )
  )
}

private SourceOutNode getIndirectReturnOutNode(CallInstruction call, int d) {
  d > 0 and
  result.getReturnKind().isReturnValue(d) and
  result.getCall().asCallInstruction() = call
}

/**
 * Gets the instruction that holds the `output` for `call`.
 */
bindingset[d]
Node callOutput(CallInstruction call, FunctionOutput output, int d) {
  exists(DataFlow::Node n, int indirectionIndex |
    n = TStageNode(FinalStage::callOutput(call, output, indirectionIndex)) and d > 0
  |
    // The return value
    result = TStageNode(FinalStage::callOutput(call, output, indirectionIndex + d))
    or
    // If there isn't an indirect out node for the call with indirection `d` then
    // we conflate this with the underlying `CallInstruction`.
    not exists(getIndirectReturnOutNode(call, indirectionIndex + d)) and
    n = result
  )
}
