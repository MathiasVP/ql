/**
 * @name Constant array overflow
 * @description Dereferencing a pointer that points past a statically-sized array is undefined behavior
 *              and may lead to security vulnerabilities
 * @kind problem
 * @problem.severity error
 * @id cpp/constant-array-overflow
 * @tags reliability
 *       security
 *       experimental
 */

import cpp

from Expr e
where none()
select e, ""
