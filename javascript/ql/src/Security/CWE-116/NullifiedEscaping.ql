/**
 * @name Nullified escaping or unescaping
 * @description Escaping special characters in a string using a meta-character like backslash or
 *              ampersand and then later unescaping the same string using a different meta-character
 *              risks reintroducing the escaped special characters.
 * @kind path-problem
 * @problem.severity warning
 * @precision high
 * @id js/nullified-escaping
 * @tags correctness
 *       security
 *       external/cwe/cwe-116
 *       external/cwe/cwe-20
 */

import javascript
import DataFlow::PathGraph
import StringReplacement

class EscapingStatus extends DataFlow::FlowLabel {
  EscapingStatus() {
    exists(Replacement replacement, string metachar |
      replacement.escapes(_, metachar) and
      this = "escaped(" + metachar + ")"
    )
  }
}

class Configuration extends DataFlow::Configuration {
  Configuration() { this = "NullifiedEscaping" }

  override predicate isSource(DataFlow::Node nd, DataFlow::FlowLabel lbl) { isSource(_, nd, lbl) }

  predicate isSource(Replacement r, DataFlow::Node nd, DataFlow::FlowLabel lbl) {
    nd = r.getInput() and
    lbl = DataFlow::FlowLabel::data()
  }

  override predicate isAdditionalFlowStep(
    DataFlow::Node pred, DataFlow::Node succ, DataFlow::FlowLabel inlbl, DataFlow::FlowLabel outlbl
  ) {
    exists(Replacement replacement, string metachar |
      pred = replacement.getInput() and
      succ = replacement.getOutput()
    |
      inlbl = DataFlow::FlowLabel::data() and
      replacement.escapes(_, metachar) and
      outlbl = "escaped(" + metachar + ")"
      or
      inlbl = "escaped(" + metachar + ")" and
      replacement.unescapes(metachar, _) and
      outlbl = DataFlow::FlowLabel::data()
    )
  }

  override predicate isSink(DataFlow::Node nd, DataFlow::FlowLabel lbl) { isSink(_, nd, lbl, _) }

  predicate isSink(Replacement r, DataFlow::Node nd, DataFlow::FlowLabel lbl, string metachar) {
    exists(string otherMetachar | otherMetachar != metachar |
      nd = r.getInput() and
      lbl = "escaped(" + metachar + ")" and
      r.unescapes(otherMetachar, _)
    )
  }

  override predicate isBarrier(DataFlow::Node nd) {
    nd = DataFlow::ssaDefinitionNode(any(SsaVariableCapture cap))
  }
}

from
  Configuration cfg, DataFlow::PathNode source, DataFlow::PathNode sink, Replacement escape,
  Replacement unescape, string metachar
where
  cfg.hasFlowPath(source, sink) and
  cfg.isSource(escape, source.getNode(), _) and
  cfg.isSink(unescape, sink.getNode(), _, metachar)
select unescape, source, sink, "This replacement nullifies escaping using '" + metachar + "' $@..",
  escape, "here"
