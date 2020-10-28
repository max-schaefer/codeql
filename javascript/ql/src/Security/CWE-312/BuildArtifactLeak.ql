/**
 * @name Storage of sensitive information in build artifact
 * @description Including sensitive information in a build artifact can
 *              expose it to an attacker.
 * @kind path-problem
 * @problem.severity error
 * @precision high
 * @id js/build-artifact-leak
 * @tags security
 *       external/cwe/cwe-312
 *       external/cwe/cwe-315
 *       external/cwe/cwe-359
 */

import javascript
import semmle.javascript.security.dataflow.BuildArtifactLeak::BuildArtifactLeak
import DataFlow::PathGraph

string describe(DataFlow::Node nd) {
  if nd instanceof CleartextLogging::Source
  then result = nd.(CleartextLogging::Source).describe()
  else result = "this code"
}

from Configuration cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink.getNode(), source, sink,
  "Sensitive data returned by $@ is stored in a build artifact here.", source.getNode(),
  describe(source.getNode())
