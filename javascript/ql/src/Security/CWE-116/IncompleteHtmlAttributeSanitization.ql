/**
 * @name Incomplete HTML attribute sanitization
 * @description Writing incompletely sanitized values to HTML
 *              attribute strings can lead to a cross-site
 *              scripting vulnerability.
 * @kind path-problem
 * @problem.severity warning
 * @precision high
 * @id js/incomplete-html-attribute-sanitization
 * @tags security
 *       external/cwe/cwe-079
 *       external/cwe/cwe-116
 *       external/cwe/cwe-020
 */

import javascript
import DataFlow::PathGraph
import semmle.javascript.security.dataflow.IncompleteHtmlAttributeSanitization::IncompleteHtmlAttributeSanitization
import semmle.javascript.security.IncompleteBlacklistSanitizer

/**
 * Gets a pretty string of the dangerous characters for `sink`.
 */
string prettyPrintDangerousCharacters(DataFlow::Node sink) {
  if sink instanceof Sink
  then
    result =
      strictconcat(string s |
        s = describeCharacters(sink.(Sink).getADangerousCharacter())
      |
        s, ", " order by s
      ).regexpReplaceAll(",(?=[^,]+$)", " or")
  else result = "dangerous characters"
}

from Configuration cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink.getNode(), source, sink,
  // this message is slightly sub-optimal as we do not have an easy way
  // to get the flow labels that reach the sink, so the message includes
  // all of them in a disjunction
  "Cross-site scripting vulnerability as the output of $@ may contain " +
    prettyPrintDangerousCharacters(sink.getNode()) + " when it reaches this attribute definition.",
  source.getNode(), "this final HTML sanitizer step"
