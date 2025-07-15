/**
 * @name Uncontrolled data in SQL query
 * @description Including user-supplied data in a SQL query without
 *              neutralizing special elements can make code vulnerable
 *              to SQL Injection.
 * @kind path-problem
 * @problem.severity error
 * @security-severity 8.8
 * @precision high
 * @id cpp/sql-injection
 * @tags security
 *       external/cwe/cwe-089
 */

import cpp
import semmle.code.cpp.security.Security
import semmle.code.cpp.security.FlowSources
import semmle.code.cpp.ir.IR
import semmle.code.cpp.ir.dataflow.TaintTracking
import SqlTainted::PathGraph

Expr asSinkExpr(DataFlow::Node node) {
  result = node.asIndirectArgument()
  or
  // We want the conversion so we only get one node for the expression
  result = node.asExpr()
}

module SqlTaintedConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node node) { node instanceof FlowSource }

  predicate isSink(DataFlow::Node node) {
    exists(Function f, Call call, int i |
      call.getTarget() = f and
      sqlArgument(f.getName(), i) and
      call.getArgument(i) = asSinkExpr(node)
    )
    or
    // sink defined using models-as-data
    sinkNode(node, "sql-injection")
  }

  predicate isBarrier(DataFlow::Node node) {
    node.asExpr().getUnspecifiedType() instanceof IntegralType
  }

  predicate isBarrierIn(DataFlow::Node node) {
    exists(SqlBarrierFunction sql, int arg, FunctionInput input |
      node.asIndirectArgument() = sql.getACallToThisFunction().getArgument(arg) and
      input.isParameterDeref(arg) and
      sql.barrierSqlArgument(input, _)
    )
  }
}

module SqlTainted = TaintTracking::Global<SqlTaintedConfig>;

from FlowSource taintSource, SqlTainted::PathNode sourceNode, SqlTainted::PathNode sinkNode
where
  SqlTainted::flowPath(sourceNode, sinkNode) and
  taintSource = sourceNode.getNode()
select sinkNode.getNode(), sourceNode, sinkNode,
  "This argument to a SQL query function is derived from $@.", taintSource,
  "user input (" + taintSource.getSourceType() + ")"
