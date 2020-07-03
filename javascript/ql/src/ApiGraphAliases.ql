/**
 * @name API-graph aliases
 * @description The number of nodes for which we found one or more aliases through the API graph.
 *              Higher is generally better.
 * @kind metric
 * @metricType project
 * @metricAggregate sum
 * @tags meta
 * @id js/meta/api-graph-aliases
 */

import javascript
import ApiGraphMetrics

select projectRoot(), count(DataFlow::Node node | nodeHasAliases(node))
