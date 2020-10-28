/**
 * @name Clear text storage of sensitive information
 * @description Sensitive information stored without encryption or hashing can expose it to an
 *              attacker.
 * @kind path-problem
 * @problem.severity error
 * @precision high
 * @id js/clear-text-storage-of-sensitive-data
 * @tags security
 *       external/cwe/cwe-312
 *       external/cwe/cwe-315
 *       external/cwe/cwe-359
 */

import javascript
import semmle.javascript.security.dataflow.CleartextStorage::CleartextStorage
import DataFlow::PathGraph

string describe(DataFlow::Node nd) {
  if nd instanceof Source then result = nd.(Source).describe() else result = "this code"
}

from Configuration cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink.getNode(), source, sink, "Sensitive data returned by $@ is stored here.",
  source.getNode(), describe(source.getNode())
