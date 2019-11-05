/**
 * @name Double escaping or unescaping
 * @description When escaping special characters using a meta-character like backslash or
 *              ampersand, the meta-character has to be escaped first to avoid double-escaping,
 *              and conversely it has to be unescaped last to avoid double-unescaping.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id js/double-escaping
 * @tags correctness
 *       security
 *       external/cwe/cwe-116
 *       external/cwe/cwe-20
 */

import javascript

/**
 * Gets a predecessor of `nd` that is not an SSA phi node.
 */
DataFlow::Node getASimplePredecessor(DataFlow::Node nd) {
  result = nd.getAPredecessor() and
  not exists(SsaDefinition ssa |
    ssa = nd.(DataFlow::SsaDefinitionNode).getSsaVariable().getDefinition()
  |
    ssa instanceof SsaPhiNode or
    ssa instanceof SsaVariableCapture
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
   * `&lt;`) using `<`.
   */
  predicate unescapes(string metachar, string char) {
    exists(string regexp, string orig |
      escapingScheme(metachar, regexp) and
      replaces(orig, char) and
      orig.regexpMatch(regexp)
    )
  }

  /**
   * Gets the previous replacement in this chain of replacements.
   */
  Replacement getPreviousReplacement() { result.getOutput() = getASimplePredecessor*(getInput()) }

  /**
   * Gets the next replacement in this chain of replacements.
   */
  Replacement getNextReplacement() { this = result.getPreviousReplacement() }

  /**
   * Gets an earlier replacement in this chain of replacements that
   * performs an escaping.
   */
  Replacement getAnEarlierEscaping(string metachar) {
    exists(Replacement pred | pred = this.getPreviousReplacement() |
      if pred.escapes(_, metachar)
      then result = pred
      else (
        not pred.unescapes(metachar, _) and result = pred.getAnEarlierEscaping(metachar)
      )
    )
  }

  /**
   * Gets an earlier replacement in this chain of replacements that
   * performs a unescaping.
   */
  Replacement getALaterUnescaping(string metachar) {
    exists(Replacement succ | this = succ.getPreviousReplacement() |
      if succ.unescapes(metachar, _)
      then result = succ
      else (
        not succ.escapes(_, metachar) and result = succ.getALaterUnescaping(metachar)
      )
    )
  }
}

/**
 * A call to `String.prototype.replace` that replaces all instances of a pattern.
 */
class GlobalStringReplacement extends Replacement, ReplaceCall {
  GlobalStringReplacement() {
    isGlobal()
  }

  override predicate replaces(string input, string output) {
    ReplaceCall.super.replaces(input, output)
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

/**
 * A string replacement wrapped in a utility function.
 */
class WrappedReplacement extends Replacement, DataFlow::CallNode {
  int i;

  Replacement inner;

  WrappedReplacement() {
    exists(DataFlow::FunctionNode wrapped | wrapped.getFunction() = getACallee() |
      wrapped.getParameter(i).flowsTo(inner.getPreviousReplacement*().getInput()) and
      inner.getNextReplacement*().getOutput().flowsTo(wrapped.getAReturn())
    )
  }

  override predicate replaces(string input, string output) { inner.replaces(input, output) }

  override DataFlow::Node getInput() { result = getArgument(i) }

  override DataFlow::SourceNode getOutput() { result = this }
}

from Replacement primary, Replacement supplementary, string message, string metachar
where
  primary.escapes(metachar, _) and
  supplementary = primary.getAnEarlierEscaping(metachar) and
  message = "may double-escape '" + metachar + "' characters from $@"
  or
  primary.unescapes(_, metachar) and
  supplementary = primary.getALaterUnescaping(metachar) and
  message = "may produce '" + metachar + "' characters that are double-unescaped $@"
select primary, "This replacement " + message + ".", supplementary, "here"
