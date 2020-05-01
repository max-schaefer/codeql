/**
 * @name API graph
 * @description Shows the API graph of a database.
 * @kind graph
 * @id js/api-graph
 */

import javascript
import ApiGraphs

query predicate nodes(LocalApiGraph::Node nd, string key, string value) {
  key = "kind" and
  value = nd.getKind().toString()
}

query predicate edges(LocalApiGraph::Node pred, LocalApiGraph::Node succ, string key, string value) {
  succ = pred.getARawSuccessor(value) and
  key = "semmle.label"
}
