/**
 * @name Use of a broken or weak cryptographic algorithm
 * @description Using broken or weak cryptographic algorithms can compromise security.
 * @kind path-problem
 * @problem.severity warning
 * @precision high
 * @id js/weak-cryptographic-algorithm
 * @tags security
 *       external/cwe/cwe-327
 */

import javascript
import semmle.javascript.security.dataflow.BrokenCryptoAlgorithm::BrokenCryptoAlgorithm
import semmle.javascript.security.SensitiveActions
import DataFlow::PathGraph

string describe(DataFlow::Node nd) {
  if nd instanceof Source then result = nd.(Source).describe() else result = "here"
}

from Configuration cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where
  cfg.hasFlowPath(source, sink) and
  not source.getNode().asExpr() instanceof CleartextPasswordExpr // flagged by js/insufficient-password-hash
select sink.getNode(), source, sink,
  "Sensitive data from $@ is used in a broken or weak cryptographic algorithm.", source.getNode(),
  describe(source.getNode())
