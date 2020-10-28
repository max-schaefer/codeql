/**
 * @name CORS misconfiguration for credentials transfer
 * @description Misconfiguration of CORS HTTP headers allows for leaks of secret credentials.
 * @kind path-problem
 * @problem.severity error
 * @precision high
 * @id js/cors-misconfiguration-for-credentials
 * @tags security
 *       external/cwe/cwe-346
 *       external/cwe/cwe-639
 */

import javascript
import semmle.javascript.security.dataflow.CorsMisconfigurationForCredentials::CorsMisconfigurationForCredentials
import DataFlow::PathGraph

DataFlow::Node getCredentialsHeader(DataFlow::Node nd) {
  if nd instanceof Sink then result = nd.(Sink).getCredentialsHeader() else result = nd
}

from Configuration cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink.getNode(), source, sink, "$@ leak vulnerability due to $@.",
  getCredentialsHeader(sink.getNode()), "Credential", source.getNode(),
  "a misconfigured CORS header value"
