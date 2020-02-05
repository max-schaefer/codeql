/**
 * @name Spurious portal node
 */

import javascript
import semmle.javascript.dataflow.Portals

from PortalNode p
where not exists(p.getPortal()) and not p instanceof MkRootNode
select p, p.getPath()
