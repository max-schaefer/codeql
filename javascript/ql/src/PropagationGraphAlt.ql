// An alternative implementation of `PropagationGraph.ql` using inter-procedural
// data flow instead of points-to.
import javascript
import NodeRepresentation

/** Holds if data read from a use of `f` may originate from an imported package. */
predicate mayComeFromLibrary(API::Node f) {
  // base case: import
  f = API::moduleImport(_)
  or
  // covariant recursive cases: members, instances, results, and promise contents
  // of something that comes from a library may themselves come from that library
  exists(API::Node base | mayComeFromLibrary(base) |
    f = base.getAMember() or
    f = base.getInstance() or
    f = base.getReturn() or
    f = base.getPromised()
  )
  or
  // contravariant recursive case: parameters of something that escapes to a library
  // may come from that library
  exists(API::Node base | mayEscapeToLibrary(base) | f = base.getAParameter())
}

/**
 * Holds if data written to a definition of `f` may flow to an imported package.
 */
predicate mayEscapeToLibrary(API::Node f) {
  // covariant recursive case: members, instances, results, and promise contents of something that
  // escapes to a library may themselves escape to that library
  exists(API::Node base | mayEscapeToLibrary(base) |
    f = base.getAMember() or
    f = base.getInstance() or
    f = base.getReturn() or
    f = base.getPromised()
  )
  or
  // contravariant recursive case: arguments passed to a function
  // that comes from a library may escape to that library
  exists(API::Node base | mayComeFromLibrary(base) | f = base.getAParameter())
}

/**
 * Holds if `pred` is a call of the form `f(..., x, ...)` and `succ` is a subsequent
 * use of `x` where the result of the call is either known to be true or known to be
 * false.
 */
private predicate guard(DataFlow::CallNode pred, DataFlow::Node succ) {
  exists(ConditionGuardNode g, SsaVariable v |
    g.getTest() = pred.asExpr() and
    pred.getAnArgument().asExpr() = v.getAUse() and
    succ.asExpr() = v.getAUse() and
    g.dominates(succ.getBasicBlock())
  )
}

/**
 * Holds if `pred` -> `succ` is a known flow step for which we have a model.
 */
predicate knownStep(DataFlow::Node pred, DataFlow::Node succ) {
  // exclude known flow/taint step
  any(TaintTracking::AdditionalTaintStep s).step(pred, succ)
  or
  exists(DataFlow::AdditionalFlowStep s |
    s.step(pred, succ) or
    s.step(pred, succ, _, _) or
    s.loadStep(pred, succ, _) or
    s.storeStep(pred, succ, _) or
    s.loadStoreStep(pred, succ, _)
  )
}

/**
 * Gets a candidate representation for `nd`, filtering out very general representations.
 */
string candidateRep(DataFlow::Node nd, boolean asRhs) {
  result = candidateRep(nd, _, asRhs) and
  // exclude some overly general representations like `(member data *)` or
  // `(parameter 0 (member exports *))`
  not result.regexpMatch("\\((parameter|member) \\w+ (\\*|\\(member exports \\*\\))\\)") and
  not result.regexpMatch("\\(root .*\\)")
}

/**
 * Gets a representation for `nd` that is not extremely rare, that is, it occurs at least five
 * times.
 */
string rep(DataFlow::Node nd, boolean asRhs) {
  result = candidateRep(nd, asRhs) and
  count(DataFlow::Node nd2 | result = candidateRep(nd2, asRhs)) >= 5
}

/**
 * Holds if `u` is a candidate for a taint source.
 */
predicate isSourceCandidate(API::Node nd, DataFlow::Node u) {
  mayComeFromLibrary(nd) and
  not nd = API::moduleImport(_) and
  u = nd.getAnImmediateUse() and
  exists(rep(u, false)) and
  not knownStep(_, u) and
  (
    u instanceof DataFlow::CallNode and
    not u = any(Import i).getImportedModuleNode()
    or
    u instanceof DataFlow::ParameterNode
  )
}

/**
 * Holds if `u` is a candidate for a sanitiser.
 */
predicate isSanitizerCandidate(DataFlow::CallNode u) {
  exists(rep(u, false)) and
  not u = any(Import i).getImportedModuleNode()
}

/**
 * Holds if `d` is a candidate for a taint sink.
 */
predicate isSinkCandidate(API::Node nd, DataFlow::Node d) {
  mayEscapeToLibrary(nd) and
  d = nd.getARhs() and
  not knownStep(d, _) and
  exists(rep(d, true)) and
  (
    d = any(ReturnStmt ret).getExpr().flow()
    or
    exists(DataFlow::InvokeNode invk |
      d = invk.(DataFlow::MethodCallNode).getReceiver() or
      d = invk.getAnArgument()
    )
  )
}

/**
 * Holds if step `pred` -> `succ` should be considered for the propagation graph.
 */
predicate step(DataFlow::Node pred, DataFlow::Node succ) {
  TaintTracking::localTaintStep(pred, succ)
  or
  succ.(DataFlow::SourceNode).hasPropertyWrite(_, pred)
  or
  succ.(DataFlow::CallNode).getAnArgument() = pred
  or
  guard(pred, succ)
}

/**
 * Gets a node that is reachable from a source candidate in the propagation graph.
 */
DataFlow::Node reachableFromSourceCandidate(DataFlow::Node src, DataFlow::TypeTracker t) {
  isSourceCandidate(_, result) and
  src = result and
  t.start()
  or
  step(reachableFromSourceCandidate(src, t), result)
  or
  exists(DataFlow::TypeTracker t2 | t = t2.smallstep(reachableFromSourceCandidate(src, t2), result))
}

/**
 * Gets a node that is reachable from a source candidate through a sanitiser candidate
 * in the propagation graph.
 */
DataFlow::Node reachableFromSanitizerCandidate(DataFlow::Node san, DataFlow::TypeTracker t) {
  isSanitizerCandidate(san) and
  exists(DataFlow::Node src |
    san = reachableFromSourceCandidate(src, DataFlow::TypeTracker::end()) and
    src != san
  ) and
  result = san and
  t.start()
  or
  step(reachableFromSanitizerCandidate(san, t), result)
  or
  exists(StepSummary summary | t = aux(san, result, summary).append(summary))
}

private import semmle.javascript.dataflow.internal.StepSummary

pragma[noinline]
private DataFlow::TypeTracker aux(DataFlow::Node san, DataFlow::Node res, StepSummary summary) {
  StepSummary::smallstep(reachableFromSanitizerCandidate(san, result), res, summary)
}

/**
 * Holds if there is a path from `src` through `san` to `snk` in the propagation graph,
 * which are source, sanitiser, and sink candidate, respectively.
 */
predicate triple(DataFlow::Node src, DataFlow::Node san, DataFlow::Node snk) {
  san = reachableFromSourceCandidate(src, DataFlow::TypeTracker::end()) and
  src != san and
  snk = reachableFromSanitizerCandidate(san, DataFlow::TypeTracker::end()) and
  isSinkCandidate(_, snk)
}

from DataFlow::Node src, DataFlow::Node san, DataFlow::Node snk
where triple(src, san, snk)
select rep(src, false), rep(san, false), rep(snk, true)
