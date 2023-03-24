/**
 * @name Potential use after free
 * @description An allocated memory block is used after it has been freed. Behavior in such cases is undefined and can cause memory corruption.
 * @kind path-problem
 * @id cpp/use-after-free
 * @problem.severity warning
 * @security-severity 9.3
 * @tags reliability
 *       security
 *       external/cwe/cwe-416
 */

import cpp
import semmle.code.cpp.dataflow.new.DataFlow
import FlowAfterFree as Flow

module UseAfterFreeFlow = Flow::FlowFromFree<useExpr/2>;

predicate useExpr(DataFlow::Node dfe, Expr e) {
  e = dfe.asExpr() and
  (
    e = any(ReturnStmt rs).getExpr() or
    alwaysDerefs(_, _, e) or
    e = any(PointerDereferenceExpr pde).getOperand() or
    e = any(PointerFieldAccess pfa).getQualifier() or
    e = any(ArrayExpr ae).getArrayBase()
  )
}

predicate useExpr0(DataFlow::Node dfe, Expr e) {
  e = dfe.asExpr() and
  (
    e = any(PointerDereferenceExpr pde).getOperand() or
    e = any(PointerFieldAccess pfa).getQualifier() or
    e = any(ArrayExpr ae).getArrayBase()
  )
}

predicate flowsFromParameter(DataFlow::Node n) {
  exists(Expr e | flowsToFree(n, e) |
    exists(Parameter p |
      n.asParameter() = p and
      bbPostDominates(e.getBasicBlock(), p.getFunction().getBlock())
    )
    or
    exists(DataFlow::Node prev |
      flowsFromParameter(prev) and
      DataFlow::localFlowStep(prev, n)
    )
  )
}

predicate isSink(DataFlow::Node n, Expr e) {
  useExpr0(n, e)
  or
  exists(FunctionCall fc, int i |
    n.asExpr() = e and
    fc.getArgument(i) = e and
    alwaysDerefs(fc, i, _)
  )
  or
  // Always assume that functions without a body will dereference the pointer.
  exists(FunctionCall fc, Function f |
    fc.getTarget() = f and
    fc.getAnArgument() = e and
    not exists(f.getBlock())
  )
}

predicate flowsToFree(DataFlow::Node n, Expr e) {
  isSink(n, e)
  or
  exists(DataFlow::Node succ |
    flowsToFree(succ, e) and
    DataFlow::localFlowStep(n, succ)
  )
}

predicate alwaysDerefs(FunctionCall fc, int i, Expr e) {
  exists(DataFlow::ParameterNode p |
    fc.getArgument(i) = e and
    fc.getTarget().getParameter(i) = p.asParameter() and
    flowsFromParameter(p)
  )
}

query predicate edges = UseAfterFreeFlow::step/2;

from DataFlow::Node dfe1, DataFlow::Node dfe2, Expr e1, Expr e2
where UseAfterFreeFlow::flows(dfe1, dfe2, e1, e2)
select e2, dfe1, dfe2, "Memory pointed to by '" + e1.toString() + "' may have $@.", e1,
  "been previously freed"
