import cpp
import utils.test.dataflow.FlowTestCommon
import semmle.code.cpp.ir.dataflow.TaintTracking

module Config implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node node) {
    node.asExpr().(FunctionCall).getTarget().hasName("source")
  }

  predicate isSink(DataFlow::Node node) {
    exists(FunctionCall call, Expr arg |
      call.getTarget().hasName("sink") and arg = call.getArgument(0)
    |
      if arg.getUnspecifiedType() instanceof ReferenceType
      then node.asConvertedExpr() = arg.getFullyConverted()
      else node.asExpr() = arg
    )
  }
}

module Flow = TaintTracking::Global<Config>;

import MakeTest<IRFlowTest<Flow>>
