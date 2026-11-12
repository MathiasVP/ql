import utils.test.dataflow.FlowTestCommon
import cpp
import semmle.code.cpp.security.FlowSources
import codeql.dataflow.test.ProvenancePathGraph

module IRTest {
  private import semmle.code.cpp.ir.IR
  private import semmle.code.cpp.ir.dataflow.TaintTracking

  /** Common data flow configuration to be used by tests. */
  module TestAllocationConfig implements DataFlow::ConfigSig {
    predicate isSource(DataFlow::Node source) {
      // external flow source node
      sourceNode(source, _)
      or
      // test source function
      source.asExpr().(FunctionCall).getTarget().getName() = "source"
    }

    predicate isSink(DataFlow::Node sink) {
      // external flow sink node
      sinkNode(sink, _)
      or
      // test sink function
      exists(FunctionCall call |
        call.getTarget().getName() = "sink" and
        exists(Expr arg | arg = call.getAnArgument() |
          if arg.getUnspecifiedType() instanceof ReferenceType
          then sink.asConvertedExpr() = arg.getFullyConverted()
          else sink.asExpr() = arg
        )
      )
    }
  }

  module IRFlow = TaintTracking::Global<TestAllocationConfig>;
}

import MakeTest<IRFlowTest<IRTest::IRFlow>>
import ShowProvenance<interpretModelForTest/2, IRTest::IRFlow::PathNode, IRTest::IRFlow::PathGraph>
