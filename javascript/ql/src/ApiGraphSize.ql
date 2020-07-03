/**
 * @name API-graph size
 * @description The number of nodes in the API graph; lower is generally better, assuming the number
 *              of aliases stays roughly the same.
 * @kind metric
 * @metricType project
 * @metricAggregate sum
 * @tags meta
 * @id js/meta/api-graph-size
 */

import javascript
import ApiGraphMetrics

select projectRoot(),
  count(LocalApiGraph::Node nd | exists(relevantReferenceTo(nd)))