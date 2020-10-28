/**
 * @name Uncontrolled data used in network request
 * @description Sending network requests with user-controlled data allows for request forgery attacks.
 * @kind path-problem
 * @problem.severity error
 * @precision medium
 * @id js/request-forgery
 * @tags security
 *       external/cwe/cwe-918
 */

import javascript
import semmle.javascript.security.dataflow.RequestForgery::RequestForgery
import DataFlow::PathGraph

DataFlow::Node getRequest(DataFlow::Node nd) {
  if nd instanceof Sink then result = nd.(Sink).getARequest() else result = nd
}

string getKind(DataFlow::Node nd) {
  if nd instanceof Sink then result = nd.(Sink).getKind() else result = "details"
}

from Configuration cfg, DataFlow::PathNode source, DataFlow::PathNode sink, DataFlow::Node request
where
  cfg.hasFlowPath(source, sink) and
  request = getRequest(sink.getNode())
select request, source, sink, "The $@ of this request depends on $@.", sink.getNode(),
  getKind(sink.getNode()), source, "a user-provided value"
