/**
 * @name PortalGraph
 * @description Insert description here...
 * @kind graph
 */

import javascript
import semmle.javascript.dataflow.Portals

query predicate nodes(PortalNode nd) {
	any()
}

query predicate edges(PortalNode pred, PortalNode succ, string key, string value) {
	portalEdge(pred, value, succ) and
	key = "semmle.label"
}
