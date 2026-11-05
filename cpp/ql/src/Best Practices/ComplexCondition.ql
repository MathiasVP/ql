/**
 * @name Complex condition
 * @description Boolean expressions that are too deeply nested are hard to read and understand. Consider naming intermediate results as local variables.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id cpp/complex-condition
 * @tags quality
 *       testability
 *       readability
 *       maintainability
 *       complexity
 *       statistical
 *       non-attributable
 */

import cpp

predicate logicalOp(string op) { op = "&&" or op = "||" }

predicate nontrivialLogicalOperator(Operation e) {
  exists(string op |
    op = e.getOperator() and
    logicalOp(op) and
    not op = e.getParent().(Operation).getOperator()
  ) and
  not e.isInMacroExpansion()
}

// Keep the root-expression filter inside the relation being counted.
pragma[noinline]
private predicate nontrivialLogicalOperatorInRoot(Expr root, Operation op) {
  not root.getParent() instanceof Expr and
  op.getParent*() = root and
  nontrivialLogicalOperator(op)
}

from Expr e, int operators
where
  operators = strictcount(Operation op | nontrivialLogicalOperatorInRoot(e, op)) and
  operators > 5
select e, "Complex condition: too many logical operations in this expression."
