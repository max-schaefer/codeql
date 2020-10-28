/**
 * @name Client-side cross-site scripting
 * @description Writing user input directly to the DOM allows for
 *              a cross-site scripting vulnerability.
 * @kind path-problem
 * @problem.severity error
 * @precision high
 * @id js/xss
 * @tags security
 *       external/cwe/cwe-079
 *       external/cwe/cwe-116
 */

import javascript
import semmle.javascript.security.dataflow.DomBasedXss::DomBasedXss
import DataFlow::PathGraph

string getKind(DataFlow::Node nd) {
  if nd instanceof Sink then result = nd.(Sink).getVulnerabilityKind() else result = "XSS"
}

from Configuration cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink.getNode(), source, sink, getKind(sink.getNode()) + " vulnerability due to $@.",
  source.getNode(), "user-provided value"
