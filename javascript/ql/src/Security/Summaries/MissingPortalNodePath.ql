/**
 * @name Missing entry nodes
 */

import javascript
import semmle.javascript.dataflow.Portals

from PortalNode pn
where not exists(pn.getPath())
select pn
