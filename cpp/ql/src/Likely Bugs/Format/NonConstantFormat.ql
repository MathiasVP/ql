/**
 * @name Non-constant format string
 * @description Passing a non-constant 'format' string to a printf-like function can lead
 *              to a mismatch between the number of arguments defined by the 'format' and the number
 *              of arguments actually passed to the function. If the format string ultimately stems
 *              from an untrusted source, this can be used for exploits.
 * @kind problem
 * @problem.severity recommendation
 * @security-severity 9.3
 * @precision high
 * @id cpp/non-constant-format
 * @tags maintainability
 *       correctness
 *       security
 *       external/cwe/cwe-134
 */

import semmle.code.cpp.ir.dataflow.TaintTracking
import semmle.code.cpp.commons.Printf
import semmle.code.cpp.security.FlowSources
import semmle.code.cpp.ir.dataflow.internal.ModelUtil
import semmle.code.cpp.models.interfaces.DataFlow
import semmle.code.cpp.models.interfaces.Taint
import semmle.code.cpp.ir.implementation.raw.Instruction

class UncalledFunction extends Function {
  UncalledFunction() {
    not exists(Call c | c.getTarget() = this) and
    // TODO: Need rationale here, added based on suggestion
    //but unclear of the scenario being avoided
    not this.(MemberFunction).overrides(_) and
    // Ignore functions that appear to be function pointers
    not exists(FunctionAccess fa | fa.getTarget() = this)
  }
}

/*
 * const char* means (const char)*, so the pointer is not const, the pointed to value is.
 * Grabs the base type of the underlying type of `t` if `t` is a pointer and checks `isConst()` else
 * checks on the underlying type of `t` alone.
 */
bindingset[t]
predicate hasConstSpecifier(Type t) {
  if t.getUnderlyingType() instanceof PointerType
  then t.getUnderlyingType().(PointerType).getBaseType().isConst()
  else t.getUnderlyingType().isConst()
}

/**
 * Holds if `node` is a non-constant source of data flow.
 * This is defined as either:
 * 1) a `FlowSource`
 * 2) a parameter of an 'uncalled' function
 * 3) an argument to a function with no definition that is not known to define the output through its input
 * 4) an out arg of a function with no definition that is not known to define the output through its input
 *
 * With exception to `FlowSource` all non-const values have a type that is not const
 * (declared without a `const` specifier)
 * ASSUMPTION: any const values are assumed to be static if their assignment is not seen
 * i.e., assuming users did not get non-const data and cast into a const
 *
 * The latter two cases address identifying standard string manipulation libraries as input sources
 * e.g., strcpy, but it will identify unknown function calls as possible non-constant source
 * since it cannot be determined if the out argument or return is constant.
 */
predicate isNonConst(DataFlow::Node node) {
  node instanceof FlowSource
  or
  // Parameters of uncalled functions that aren't const
  exists(UncalledFunction f, Parameter p |
    not hasConstSpecifier(p.getType()) and
    f.getAParameter() = p and
    p = node.asParameter()
  )
  or
  // Consider as an input any out arg of a function or a function's return where the function is not:
  // 1. a function with a known dataflow or taintflow from input to output and the `node` is the output
  // 2. a function where there is a known definition
  // i.e., functions that with unknown bodies and are not known to define the output through its input
  //       are considered as possible non-const sources
  // The function's output must also not be const to be considered a non-const source
  exists(Call c |
    exists(Expr arg | c.getAnArgument() = arg |
      arg = node.asDefiningArgument() and
      not hasConstSpecifier(arg.getType())
    )
    or
    c = node.asIndirectExpr() and not hasConstSpecifier(c.getType())
  ) and
  not exists(Function func, FunctionInput input, FunctionOutput output, CallInstruction call |
    // NOTE: we must include dataflow and taintflow. e.g., including only dataflow we will find sprintf
    // variant function's output are now possible non-const sources
    (
      func.(DataFlowFunction).hasDataFlow(input, output) or
      func.(TaintFunction).hasTaintFlow(input, output)
    ) and
    node = callOutput(call, output) and
    call.getStaticCallTarget() = func
  ) and
  not exists(Call c |
    c.getTarget().hasDefinition() and
    if node instanceof DataFlow::DefinitionByReferenceNode
    then c.getAnArgument() = node.asDefiningArgument()
    else c = [node.asExpr(), node.asIndirectExpr()]
  )
}

/**
 * Holds if `sink` is a sink is a format string of any
 * `FormattingFunctionCall`.
 */
predicate isSinkImpl(DataFlow::Node sink, Expr formatString) {
  [sink.asExpr(), sink.asIndirectExpr()] = formatString and
  exists(FormattingFunctionCall fc | formatString = fc.getArgument(fc.getFormatParameterIndex()))
}

module NonConstFlowConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) { isNonConst(source) }

  predicate isSink(DataFlow::Node sink) { isSinkImpl(sink, _) }

  predicate isBarrier(DataFlow::Node node) {
    // Ignore tracing non-const through array indices
    exists(ArrayExpr a | a.getArrayOffset() = node.asExpr())
  }
}

module NonConstFlow = TaintTracking::Global<NonConstFlowConfig>;

from FormattingFunctionCall call, Expr formatString, DataFlow::Node sink
where
  call.getArgument(call.getFormatParameterIndex()) = formatString and
  NonConstFlow::flowTo(sink) and
  isSinkImpl(sink, formatString)
select formatString,
  "The format string argument to " + call.getTarget().getName() +
    " should be constant to prevent security issues and other potential errors."
