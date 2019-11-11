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
import StringReplacement

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
 * Gets the previous replacement in a chain of replacements.
 */
Replacement getPreviousReplacement(Replacement r) {
  result.getOutput() = getASimplePredecessor*(r.getInput())
}

/**
 * Gets the next replacement in a chain of replacements.
 */
Replacement getNextReplacement(Replacement r) { r = getPreviousReplacement(result) }

/**
 * Gets an earlier replacement in a chain of replacements that
 * performs an escaping.
 */
Replacement getAnEarlierEscaping(Replacement r, string metachar) {
  exists(Replacement pred | pred = getPreviousReplacement(r) |
    if pred.escapes(_, metachar)
    then result = pred
    else (
      not pred.unescapes(metachar, _) and result = getAnEarlierEscaping(pred, metachar)
    )
  )
}

/**
 * Gets an earlier replacement in a chain of replacements that
 * performs a unescaping.
 */
Replacement getALaterUnescaping(Replacement r, string metachar) {
  exists(Replacement succ | r = getPreviousReplacement(succ) |
    if succ.unescapes(metachar, _)
    then result = succ
    else (
      not succ.escapes(_, metachar) and result = getALaterUnescaping(succ, metachar)
    )
  )
}

/**
 * A string replacement wrapped in a utility function.
 */
class WrappedReplacement extends Replacement, DataFlow::CallNode {
  int i;

  Replacement inner;

  WrappedReplacement() {
    exists(DataFlow::FunctionNode wrapped | wrapped.getFunction() = getACallee() |
      wrapped.getParameter(i).flowsTo(getPreviousReplacement*(inner).getInput()) and
      getNextReplacement*(inner).getOutput().flowsTo(wrapped.getAReturn())
    )
  }

  override predicate replaces(string input, string output) { inner.replaces(input, output) }

  override DataFlow::Node getInput() { result = getArgument(i) }

  override DataFlow::SourceNode getOutput() { result = this }
}

from Replacement primary, Replacement supplementary, string message, string metachar
where
  primary.escapes(metachar, metachar) and
  supplementary = getAnEarlierEscaping(primary, metachar) and
  message = "may double-escape '" + metachar + "' characters from $@"
  or
  primary.unescapes(metachar, metachar) and
  supplementary = getALaterUnescaping(primary, metachar) and
  message = "may produce '" + metachar + "' characters that are double-unescaped $@"
select primary, "This replacement " + message + ".", supplementary, "here"
