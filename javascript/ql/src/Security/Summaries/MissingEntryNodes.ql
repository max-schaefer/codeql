/**
 * @name Missing entry nodes
 */

import javascript
import semmle.javascript.dataflow.Portals

from Portal p
where not exists(EntryNode e | p = e.getPortal())
select p, p.getAnEntryNode(_)
