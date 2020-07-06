/**
 * Provides query predicates for extracting source and sink  summaries.
 *
 * Import this from `javascript.qll` to turn on summarization for all security queries.
 */

private import javascript
private import ApiGraphs

private predicate mayEscapeToClient(LocalApiGraph::DefNode nd) {
  nd = LocalApiGraph::moduleDefinition(_)
  or
  exists(LocalApiGraph::Node base | mayComeFromClient(base) |
    nd = base.getAParameter() or
    nd = base.getInstance()
  )
  or
  exists(LocalApiGraph::Node base | mayEscapeToClient(base) |
    nd = base.getAMember() or
    nd = base.getResult() or
    nd = base.getPromised()
  )
}

private predicate mayComeFromClient(LocalApiGraph::UseNode nd) {
  exists(LocalApiGraph::Node base | mayEscapeToClient(base) |
    nd = base.getAParameter() or
    nd = base.getInstance()
  )
  or
  exists(LocalApiGraph::Node base | mayComeFromClient(base) |
    nd = base.getAMember() or
    nd = base.getResult() or
    nd = base.getPromised()
  )
}

private class SinkSummarizingConfig extends DataFlow::Configuration {
  DataFlow::Configuration base;

  SinkSummarizingConfig() {
    this = "summarize sinks " + base and base.regexpMatch("(?!summarize ).*")
  }

  DataFlow::Configuration getBase() { result = base }

  override predicate isSource(DataFlow::Node nd, DataFlow::FlowLabel lbl) {
    nd = any(LocalApiGraph::Node n | mayComeFromClient(n)).getAUse() and
    lbl = any(DataFlow::FlowLabel l)
  }

  override predicate isSink(DataFlow::Node nd, DataFlow::FlowLabel lbl) {
    (base.isSink(nd) or nd.(DataFlow::AdditionalSink).isSinkFor(base)) and
    lbl = any(DataFlow::StandardFlowLabel f)
    or
    nd.(DataFlow::AdditionalSink).isSinkFor(base, lbl)
    or
    base.isSink(nd, lbl)
  }

  override predicate isBarrier(DataFlow::Node nd) { base.isBarrier(nd) }

  override predicate isBarrierGuard(DataFlow::BarrierGuardNode guard) { base.isBarrierGuard(guard) }

  override predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    base.isAdditionalFlowStep(pred, succ)
  }
}

private class SourceSummarizingConfig extends DataFlow::Configuration {
  DataFlow::Configuration base;

  SourceSummarizingConfig() {
    this = "summarize sources " + base and base.regexpMatch("(?!summarize ).*")
  }

  DataFlow::Configuration getBase() { result = base }

  override predicate isSource(DataFlow::Node nd, DataFlow::FlowLabel lbl) {
    (base.isSource(nd) or nd.(DataFlow::AdditionalSource).isSourceFor(base)) and
    lbl = base.getDefaultSourceLabel()
    or
    nd.(DataFlow::AdditionalSource).isSourceFor(base, lbl)
    or
    base.isSource(nd, lbl)
  }

  override predicate isSink(DataFlow::Node nd, DataFlow::FlowLabel lbl) {
    nd = any(LocalApiGraph::Node n | mayEscapeToClient(n)).getADefinition() and
    lbl = any(DataFlow::FlowLabel l)
  }

  override predicate isBarrier(DataFlow::Node nd) { base.isBarrier(nd) }

  override predicate isBarrierGuard(DataFlow::BarrierGuardNode guard) { base.isBarrierGuard(guard) }

  override predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    base.isAdditionalFlowStep(pred, succ)
  }
}

query predicate sinkSummary(
  string tag, LocalApiGraph::Node u, DataFlow::FlowLabel lbl, DataFlow::Configuration base
) {
  tag = "sinkSummary" and
  exists(
    SinkSummarizingConfig cfg, DataFlow::SourcePathNode source, DataFlow::SinkPathNode sink,
    DataFlow::MidPathNode last
  |
    cfg = source.getConfiguration() and
    last = source.getASuccessor*() and
    sink = last.getASuccessor() and
    u.getAUse() = source.getNode() and
    // avoid constructing infeasible paths
    last.getPathSummary().hasReturn() = false
  |
    lbl = last.getPathSummary().getStartLabel() and
    base = cfg.getBase()
  )
}

query predicate sourceSummary(
  string tag, LocalApiGraph::Node d, DataFlow::FlowLabel lbl, DataFlow::Configuration base
) {
  tag = "sourceSummary" and
  exists(
    SourceSummarizingConfig cfg, DataFlow::SourcePathNode source, DataFlow::SinkPathNode sink,
    DataFlow::MidPathNode last
  |
    cfg = source.getConfiguration() and
    last = source.getASuccessor*() and
    sink = last.getASuccessor() and
    d.getADefinition() = sink.getNode() and
    // avoid constructing infeasible paths
    last.getPathSummary().hasCall() = false
  |
    lbl = last.getPathSummary().getEndLabel().toString() and
    base = cfg.getBase()
  )
}
