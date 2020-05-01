import ApiGraphs

int loc() { result = sum(File f | | f.getNumberOfLinesOfCode()) }

int representableNodes() {
  result = count(LocalApiGraph::Node nd | | [nd.getAUse(), nd.getADefinition()])
}

LocalApiGraph::Node origin(DataFlow::Node nd) { nd = result.getAUse() }

int aliasedPairs() {
  result = count(DataFlow::Node nd1, DataFlow::Node nd2 | origin(nd1) = origin(nd2) and nd1 != nd2)
}

select loc() as LinesOfCode, count(DataFlow::Node nd) as DataFlowNodes,
  count(DataFlow::Node pred, DataFlow::Node succ | succ = pred.getASuccessor()) as DataFlowEdges,
  count(LocalApiGraph::Node nd) as ApiGraphNodes,
  count(LocalApiGraph::Node pred, string lbl, LocalApiGraph::Node succ |
    succ = pred.getARawSuccessor(lbl)
  ) as ApiGraphEdges, representableNodes() as RepresentableNode, aliasedPairs() as AliasedPairs
