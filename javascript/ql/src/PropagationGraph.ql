import javascript
import PropagationGraphs

predicate reachableFromSourceCandidate(
  PropagationGraph::SourceCandidate src, PropagationGraph::Node nd
) {
  PropagationGraph::edge(src, nd)
  or
  exists(PropagationGraph::Node mid |
    reachableFromSourceCandidate(src, mid) and
    PropagationGraph::edge(mid, nd)
  )
}

predicate reachableFromSanitizerCandidate(
  PropagationGraph::SanitizerCandidate san, PropagationGraph::Node nd
) {
  PropagationGraph::edge(san, nd)
  or
  exists(PropagationGraph::Node mid |
    reachableFromSanitizerCandidate(san, mid) and
    PropagationGraph::edge(mid, nd)
  )
}

predicate triple(
  PropagationGraph::SourceCandidate src, PropagationGraph::SanitizerCandidate san,
  PropagationGraph::SinkCandidate snk
) {
  reachableFromSourceCandidate(src, san) and
  src.asDataFlowNode().getEnclosingExpr() != san.asDataFlowNode().getEnclosingExpr() and
  reachableFromSanitizerCandidate(san, snk)
  // NB: we do not require `san` and `snk` to be different, since we might have a situation like
  // `sink(sanitize(src))` where `san` and `snk` are both `sanitize(src)`
}

from PropagationGraph::Node src, PropagationGraph::Node san, PropagationGraph::Node snk
where triple(src, san, snk)
select src, san, snk
