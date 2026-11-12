import cpp
import semmle.code.cpp.dataflow.new.DataFlow
import utils.test.InlineExpectationsTest

module FromVariableConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) { source.asVariable() instanceof GlobalVariable }

  predicate isSink(DataFlow::Node sink) {
    exists(FunctionCall call |
      call.getTarget().hasName("sink") and
      sink.asExpr() = call.getAnArgument()
    )
  }
}

module FromVariableFlow = DataFlow::Global<FromVariableConfig>;

module ToVariableConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) {
    source.asExpr() = any(GlobalVariable v).getInitializer().getExpr()
  }

  predicate isSink(DataFlow::Node sink) { sink.asVariable() instanceof GlobalVariable }
}

module ToVariableFlow = DataFlow::Global<ToVariableConfig>;

module AsVariableTest implements TestSig {
  string getARelevantTag() { result = ["asVariable", "initializer"] }

  predicate hasActualResult(Location location, string element, string tag, string value) {
    exists(DataFlow::Node source, DataFlow::Node sink |
      FromVariableFlow::flow(source, sink) and
      location = sink.getLocation() and
      element = sink.toString() and
      tag = "asVariable" and
      value = source.asVariable().getName()
      or
      ToVariableFlow::flow(source, sink) and
      location = sink.asVariable().getLocation() and
      element = sink.toString() and
      tag = "initializer" and
      value = ""
    )
  }
}

import MakeTest<AsVariableTest>
