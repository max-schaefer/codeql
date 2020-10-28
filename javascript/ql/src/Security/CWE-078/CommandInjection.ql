/**
 * @name Uncontrolled command line
 * @description Using externally controlled strings in a command line may allow a malicious
 *              user to change the meaning of the command.
 * @kind path-problem
 * @problem.severity error
 * @precision high
 * @id js/command-line-injection
 * @tags correctness
 *       security
 *       external/cwe/cwe-078
 *       external/cwe/cwe-088
 */

import javascript
import semmle.javascript.security.dataflow.CommandInjection::CommandInjection
import DataFlow::PathGraph

string getSourceType(DataFlow::Node nd) {
  if nd instanceof Source then result = nd.(Source).getSourceType() else result = "user input"
}

from Configuration cfg, DataFlow::PathNode source, DataFlow::PathNode sink, DataFlow::Node highlight
where
  cfg.hasFlowPath(source, sink) and
  (
    if cfg.isSinkWithHighlight(sink.getNode(), _)
    then cfg.isSinkWithHighlight(sink.getNode(), highlight)
    else highlight = sink.getNode()
  )
select highlight, source, sink, "This command depends on $@.", source.getNode(),
  getSourceType(source.getNode())
