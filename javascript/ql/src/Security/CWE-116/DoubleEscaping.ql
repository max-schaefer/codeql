/**
 * @name Double escaping or unescaping
 * @description When escaping special characters using a meta-character like backslash or
 *              ampersand, the meta-character has to be escaped first to avoid double-escaping,
 *              and conversely it has to be unescaped last to avoid double-unescaping.
 * @kind path-problem
 * @problem.severity warning
 * @precision high
 * @id js/double-escaping
 * @tags correctness
 *       security
 *       external/cwe/cwe-116
 *       external/cwe/cwe-20
 */

import javascript
import DataFlow::PathGraph

/**
 * Holds if `rl` is a simple constant, which is bound to the result of the predicate.
 *
 * For example, `/a/g` has string value `"a"` and `/abc/` has string value `"abc"`,
 * while `/ab?/` and `/a(?=b)/` do not have a string value.
 *
 * Flags are ignored, so `/a/i` is still considered to have string value `"a"`,
 * even though it also matches `"A"`.
 *
 * Note the somewhat subtle use of monotonic aggregate semantics, which makes the
 * `strictconcat` fail if one of the children of the root is not a constant (legacy
 * semantics would simply skip such children).
 */
language[monotonicAggregates]
string getStringValue(RegExpLiteral rl) {
  exists(RegExpTerm root | root = rl.getRoot() |
    result = root.(RegExpConstant).getValue()
    or
    result = strictconcat(RegExpTerm ch, int i |
        ch = root.(RegExpSequence).getChild(i)
      |
        ch.(RegExpConstant).getValue() order by i
      )
  )
}

/**
 * Holds if `metachar` is a meta-character that is used to escape special characters
 * into a form described by regular expression `regex`.
 */
predicate escapingScheme(string metachar, string regex) {
  metachar = "&" and regex = "&.+;"
  or
  metachar = "%" and regex = "%.+"
  or
  metachar = "\\" and regex = "\\\\.+"
}

/**
 * A method call that performs string replacement.
 */
abstract class Replacement extends DataFlow::Node {
  /**
   * Holds if this replacement replaces the string `input` with `output`.
   */
  abstract predicate replaces(string input, string output);

  /**
   * Gets the input of this replacement.
   */
  abstract DataFlow::Node getInput();

  /**
   * Gets the output of this replacement.
   */
  abstract DataFlow::SourceNode getOutput();

  /**
   * Holds if this replacement escapes `char` using `metachar`.
   *
   * For example, during HTML entity escaping `<` is escaped (to `&lt;`)
   * using `&`.
   */
  predicate escapes(string char, string metachar) {
    exists(string regexp, string repl |
      escapingScheme(metachar, regexp) and
      replaces(char, repl) and
      repl.regexpMatch(regexp)
    )
  }

  /**
   * Holds if this replacement unescapes `char` using `metachar`.
   *
   * For example, during HTML entity unescaping `<` is unescaped (from
   * `&lt;`) using `&`.
   */
  predicate unescapes(string metachar, string char) {
    exists(string regexp, string orig |
      escapingScheme(metachar, regexp) and
      replaces(orig, char) and
      orig.regexpMatch(regexp)
    )
  }
}

/**
 * A call to `String.prototype.replace` that replaces all instances of a pattern.
 */
class GlobalStringReplacement extends Replacement, DataFlow::MethodCallNode {
  RegExpLiteral pattern;

  GlobalStringReplacement() {
    this.getMethodName() = "replace" and
    pattern.flow().(DataFlow::SourceNode).flowsTo(this.getArgument(0)) and
    this.getNumArgument() = 2 and
    pattern.isGlobal()
  }

  override predicate replaces(string input, string output) {
    input = getStringValue(pattern) and
    output = this.getArgument(1).getStringValue()
    or
    exists(DataFlow::FunctionNode replacer, DataFlow::PropRead pr, DataFlow::ObjectLiteralNode map |
      replacer = getCallback(1) and
      replacer.getParameter(0).flowsToExpr(pr.getPropertyNameExpr()) and
      pr = map.getAPropertyRead() and
      pr.flowsTo(replacer.getAReturn()) and
      map.asExpr().(ObjectExpr).getPropertyByName(input).getInit().getStringValue() = output
    )
  }

  override DataFlow::Node getInput() { result = this.getReceiver() }

  override DataFlow::SourceNode getOutput() { result = this }
}

/**
 * A call to `JSON.stringify`, viewed as a string replacement.
 */
class JsonStringifyReplacement extends Replacement, DataFlow::CallNode {
  JsonStringifyReplacement() { this = DataFlow::globalVarRef("JSON").getAMemberCall("stringify") }

  override predicate replaces(string input, string output) {
    input = "\\" and output = "\\\\"
    // the other replacements are not relevant for this query
  }

  override DataFlow::Node getInput() { result = this.getArgument(0) }

  override DataFlow::SourceNode getOutput() { result = this }
}

/**
 * A call to `JSON.parse`, viewed as a string replacement.
 */
class JsonParseReplacement extends Replacement {
  JsonParserCall self;

  JsonParseReplacement() { this = self }

  override predicate replaces(string input, string output) {
    input = "\\\\" and output = "\\"
    // the other replacements are not relevant for this query
  }

  override DataFlow::Node getInput() { result = self.getInput() }

  override DataFlow::SourceNode getOutput() { result = self.getOutput() }
}

class EscapingStatus extends DataFlow::FlowLabel {
  EscapingStatus() {
    exists(Replacement replacement, string metachar |
      replacement.escapes(_, metachar) and
      this = "escaped(" + metachar + ")"
      or
      replacement.unescapes(_, metachar) and
      this = "unescaped(" + metachar + ")"
    )
  }
}

class Configuration extends DataFlow::Configuration {
  Configuration() { this = "DoubleEscaping" }

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
      not replacement.escapes(metachar, _) and
      not replacement.unescapes(_, metachar) and
      outlbl = inlbl
      or
      inlbl = "escaped(" + metachar + ")" and
      replacement.unescapes(_, metachar) and
      outlbl = DataFlow::FlowLabel::data()
      or
      inlbl = DataFlow::FlowLabel::data() and
      replacement.unescapes(_, metachar) and
      outlbl = "unescaped(" + metachar + ")"
      or
      inlbl = "unescaped(" + metachar + ")" and
      not replacement.unescapes(metachar, _) and
      not replacement.escapes(_, metachar) and
      outlbl = inlbl
      or
      inlbl = "unescaped(" + metachar + ")" and
      replacement.escapes(_, metachar) and
      outlbl = DataFlow::FlowLabel::data()
    )
  }

  override predicate isSink(DataFlow::Node nd, DataFlow::FlowLabel lbl) { isSink(_, nd, lbl) }

  predicate isSink(Replacement r, DataFlow::Node nd, DataFlow::FlowLabel lbl) {
    exists(string metachar | nd = r.getInput() |
      lbl = "escaped(" + metachar + ")" and
      r.escapes(metachar, _)
      or
      lbl = "unescaped(" + metachar + ")" and
      r.unescapes(metachar, _)
    )
  }

  override predicate isBarrier(DataFlow::Node nd) {
    exists(SsaVariableCapture ssa | nd = DataFlow::ssaDefinitionNode(ssa))
  }
}

from
  Configuration cfg, DataFlow::PathNode source, DataFlow::PathNode sink, Replacement primary,
  Replacement supplementary, string message, string metachar
where
  cfg.hasFlowPath(source, sink) and
  (
    cfg.isSource(supplementary, source.getNode(), _) and
    cfg.isSink(primary, sink.getNode(), "escaped(" + metachar + ")") and
    message = "may double-escape '" + metachar + "' characters from $@"
    or
    cfg.isSource(primary, source.getNode(), _) and
    cfg.isSink(supplementary, sink.getNode(), "unescaped(" + metachar + ")") and
    message = "may produce '" + metachar + "' characters that are double-unescaped $@"
  )
select primary, source, sink, "This replacement " + message + ".", supplementary, "here"
