/**
 * @name JSON-encoded data embedded inside quotes
 * @description JSON-encoded data may contain quotes, allowing it to break out of an enclosing
 *              set of quotes.
 * @kind path-problem
 * @problem.severity warning
 * @precision high
 * @id js/quoted-json
 * @tags security
 *       external/cwe/cwe-089
 */

import javascript
import DataFlow::PathGraph

module StringBreak {
  predicate containsQuote(StringOps::ConcatenationLeaf nd, string quote, boolean initial) {
    exists(string str | str = nd.getStringValue() |
      initial = true and
      quote = str.regexpCapture("(?s)[^'\"\n]*(['\"]).*", 1)
      or
      initial = false and
      quote = str.regexpCapture("(?s).*(['\"])[^'\"\n]*", 1)
    )
  }

  class Configuration extends TaintTracking::Configuration {
    string quote;

    Configuration() {
      (quote = "'" or quote = "\"") and
      this = "StringBreak" + quote
    }

    string quoteTp() { if quote = "'" then result = "single" else result = "double" }

    override predicate isSource(DataFlow::Node nd) {
      nd = DataFlow::globalVarRef("JSON").getAMemberCall("stringify")
    }

    override predicate isSink(DataFlow::Node nd) {
      exists(StringOps::ConcatenationLeaf l | l = nd |
        containsQuote(l.getPreviousLeaf(), quote, false) and
        containsQuote(l.getNextLeaf(), quote, true)
      ) and
      not exists(DataFlow::Node msg |
        TaintTracking::localTaintStep*(nd, msg) and
        isMessage(msg)
      )
    }

    override predicate isSanitizer(DataFlow::Node nd) {
      exists(StringReplaceCall repl | repl = nd |
        repl.isGlobal() and
        repl.replaces(quote, _)
      )
      or
      exists(string encode |
        encode = "encodeURI" or encode = "encodeURIComponent" or encode = "escape"
      |
        nd = DataFlow::globalVarRef(encode).getACall()
      )
      or
      nd instanceof Base64::Encode
      or
      nd instanceof JsonParserCall
    }
  }

  bindingset[n]
  predicate messageName(string n) { n.regexpMatch("(?i)desc(ription)?|message|msg") }

  string getName(Expr e) {
    result = e.(Identifier).getName() or
    result = e.(PropAccess).getPropertyName()
  }

  predicate isMessage(DataFlow::Node nd) {
    exists(DataFlow::InvokeNode c, int i | nd = c.getArgument(i) |
      c.getCalleeName().regexpMatch("it|describe") and
      i = 0
      or
      c.getCalleeName().regexpMatch("assert.*")
      or
      messageName(c.getACallee().getParameter(i).getName())
      or
      exists(string name |
        name = getName(c.(DataFlow::MethodCallNode).getReceiver().asExpr()) or
        name = c.getCalleeName()
      |
        name.regexpMatch("(?i)_*log.*")
      )
      or
      c = DataFlow::globalVarRef("console").getAMemberCall(_)
      or
      c = DataFlow::moduleImport("invariant").getACall()
      or
      exists(string err | err.matches("%Error") |
        c = DataFlow::globalVarRef(err).getAnInstantiation()
      )
    )
    or
    exists(DataFlow::PropWrite pw | nd = pw.getRhs() | messageName(pw.getPropertyName()))
    or
    exists(Assignment assgn | nd.asExpr() = assgn.getRhs() |
      messageName(getName(assgn.getTarget()))
    )
  }
}

from StringBreak::Configuration cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink.getNode(), source, sink,
  "If this $@ contains a " + cfg.quoteTp() + " quote, it could break out of the enclosing quotes.",
  source.getNode(), "JSON value"
