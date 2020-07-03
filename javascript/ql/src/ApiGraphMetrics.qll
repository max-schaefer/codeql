import javascript
import ApiGraphs
import meta.MetaMetrics

/**
 * Gets the RHS of a definition of `nd` or a `SourceNode` that is a use of `nd`.
 *
 * Collectively we call these "relevant references".
 */
DataFlow::Node relevantReferenceTo(LocalApiGraph::Node nd) {
  result = nd.getAUse() and
  result instanceof DataFlow::SourceNode
  or
  result = nd.getADefinition()
}

/**
 * Gets the number of relevant references to `nd`.
 */
int numReferencesTo(LocalApiGraph::Node nd) { result = strictcount(relevantReferenceTo(nd)) }

/**
 * Holds if there is more than one relevant reference to `nd`.
 */
predicate accessPathHasAliases(LocalApiGraph::Node nd) { numReferencesTo(nd) > 1 }

/**
 * Holds if `node` refers to an API-graph node with more than one relevant reference,
 * implying that we have found one or more aliases for `node`.
 */
predicate nodeHasAliases(DataFlow::Node node) {
  exists(LocalApiGraph::Node n |
    node = relevantReferenceTo(n) and
    accessPathHasAliases(n)
  )
}
