/**
 * @name Overrunning write
 * @description Exceeding the size of a static array during write or access operations
 *              may result in a buffer overflow.
 * @kind problem
 * @problem.severity error
 * @id cpp/overrun-write
 * @tags reliability
 *       security
 *       experimental
 *       external/cwe/cwe-119
 *       external/cwe/cwe-131
 */

import cpp

from Expr e
where none()
select e, ""
