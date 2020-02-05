/**
 * @name Missing exit nodes
 */

import javascript
import semmle.javascript.dataflow.Portals

from Portal p
where not exists(ExitNode e | p = e.getPortal())
select p, p.getAnExitNode(_)
