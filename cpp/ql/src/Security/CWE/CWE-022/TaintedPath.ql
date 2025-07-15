/**
 * @name Uncontrolled data used in path expression
 * @description Accessing paths influenced by users can allow an
 *              attacker to access unexpected resources.
 * @kind path-problem
 * @problem.severity warning
 * @security-severity 7.5
 * @precision medium
 * @id cpp/path-injection
 * @tags security
 *       external/cwe/cwe-022
 *       external/cwe/cwe-023
 *       external/cwe/cwe-036
 *       external/cwe/cwe-073
 */

import cpp
import semmle.code.cpp.security.FlowSources
import semmle.code.cpp.ir.IR
import semmle.code.cpp.ir.dataflow.TaintTracking
import TaintedPath::PathGraph

/**
 * Holds for a variable that has any kind of upper-bound check anywhere in the program.
 * This is biased towards being inclusive and being a coarse overapproximation because
 * there are a lot of valid ways of doing an upper bounds checks if we don't consider
 * where it occurs, for example:
 * ```cpp
 *   if (x < 10) { sink(x); }
 *
 *   if (10 > y) { sink(y); }
 *
 *   if (z > 10) { z = 10; }
 *   sink(z);
 * ```
 */
predicate hasUpperBoundsCheck(Variable var) {
  exists(RelationalOperation oper, VariableAccess access |
    oper.getAnOperand() = access and
    access.getTarget() = var and
    // Comparing to 0 is not an upper bound check
    not oper.getAnOperand().getValue() = "0"
  )
}

predicate isSinkImpl(DataFlow::Node sink, Call call) {
  exists(Function f |
    exists(string nme | f.hasGlobalName(nme) |
      nme = ["fopen", "_fopen", "_wfopen", "open", "_open", "_wopen"]
      or
      // create file function on windows
      nme.matches("CreateFile%")
    )
    or
    f.hasQualifiedName("std", "fopen")
    or
    // on any of the fstream classes, or filebuf
    exists(string nme | f.getDeclaringType().hasQualifiedName("std", nme) |
      nme = ["basic_fstream", "basic_ifstream", "basic_ofstream", "basic_filebuf"]
    ) and
    // we look for either the open method or the constructor
    (f.getName() = "open" or f instanceof Constructor)
  |
    f = call.getTarget() and
    call.getArgument(0) = sink.asIndirectArgument() and
    call.getLocation().getFile().getBaseName() =
      "CWE23_Relative_Path_Traversal__char_connect_socket_fopen_44.cpp"
  )
}

module TaintedPathConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node node) { node instanceof FlowSource }

  predicate isSink(DataFlow::Node node) { isSinkImpl(node, _) }

  predicate isBarrier(DataFlow::Node node) {
    node.asExpr().(Call).getTarget().getUnspecifiedType() instanceof ArithmeticType
    or
    exists(LoadInstruction load, Variable checkedVar |
      load = node.asInstruction() and
      checkedVar = load.getSourceAddress().(VariableAddressInstruction).getAstVariable() and
      hasUpperBoundsCheck(checkedVar)
    )
  }

  predicate isBarrierOut(DataFlow::Node node) {
    // make sinks barriers so that we only report the closest instance
    isSink(node)
  }
}

module TaintedPath = TaintTracking::Global<TaintedPathConfig>;

from
  FlowSource taintSource, TaintedPath::PathNode sourceNode, TaintedPath::PathNode sinkNode,
  Call call
where
  isSinkImpl(sinkNode.getNode(), call) and
  TaintedPath::flowPath(sourceNode, sinkNode) and
  taintSource = sourceNode.getNode()
select sinkNode.getNode(), sourceNode, sinkNode,
  "This argument to a file access function is derived from $@ and then passed to " +
    call.getTarget() + ".", taintSource, "user input (" + taintSource.getSourceType() + ")"
