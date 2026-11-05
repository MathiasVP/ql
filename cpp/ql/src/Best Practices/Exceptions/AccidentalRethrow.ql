/**
 * @name Accidental rethrow
 * @description When there is nothing to rethrow, attempting to rethrow an exception will terminate the program.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/rethrow-no-exception
 * @tags quality
 *       reliability
 *       correctness
 *       error-handling
 *       exceptions
 */

import cpp

predicate isInCatch(Expr e) { e.getEnclosingStmt().getParent*() instanceof CatchBlock }

private predicate isCalledInCatch(Function f) {
  // We assume that rethrows are intended when the function is called *exception*.
  f.getName().toLowerCase().matches("%exception%")
  or
  exists(FunctionCall call | call = f.getACallToThisFunction() |
    isInCatch(call) or
    isCalledInCatch(call.getEnclosingFunction())
  )
}

from ReThrowExpr e
where
  not isInCatch(e) and
  not isCalledInCatch(e.getEnclosingFunction())
select e, "As there is no current exception, this rethrow expression will terminate the program."
