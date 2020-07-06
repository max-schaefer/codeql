/**
 * @name Extract propagation summaries
 * @description Extracts propagation summaries, that is, tuples of the form `(in, out)` representing
 *              the fact that data flowing into a definition of `in` flows out of a use of `out`.
 * @kind propagation-summary
 * @id js/propagation-summary-extraction
 */

import ApiGraphs

predicate paramUse(LocalApiGraph::Node base, LocalApiGraph::Node parm, DataFlow::Node use) {
  parm = base.getParameter(_).getASuccessor*() and
  use = parm.getAUse()
}

predicate resDef(LocalApiGraph::Node base, LocalApiGraph::Node res, DataFlow::Node def) {
  res = base.getResult().getASuccessor*() and
  def = res.getADefinition()
}

from LocalApiGraph::Node parm, LocalApiGraph::Node res
where
  exists(LocalApiGraph::Node base, DataFlow::Node nd |
    paramUse(base, parm, nd) and
    resDef(base, res, nd) and
    // only extract summaries for modules defined in this database
    base = LocalApiGraph::moduleDefinition(_).getASuccessor*()
  )
select "propagationSummary", parm, res
