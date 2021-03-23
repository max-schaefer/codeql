/**
 * @name API graph
 * @description Shows the API graph of a code base.
 * @kind graph
 * @id js/api-graph
 */

import javascript

/** Gets a string representation of the location information for `nd`. */
string locationString(API::Node nd) {
  exists(string fp, int sl, int sc, int el, int ec | nd.hasLocationInfo(fp, sl, sc, el, ec) |
    result = fp + ":" + sl + ":" + sc + ":" + el + ":" + ec
  )
}

/**
 * Gets the rank of node `nd` among all nodes ordered by depth, string representation,
 * and location.
 */
int nodeRank(API::Node nd) {
  nd =
    rank[result + 1](API::Node nd2 |
      |
      nd2 order by nd2.getDepth(), nd2.toString(), locationString(nd2)
    )
}

/**
 * Gets the rank of `lbl` among all labels on outgoing edges of `pred`, ordered alphabetically.
 */
int labelRank(API::Node pred, string lbl, API::Node succ) {
  lbl + "->" + nodeRank(succ) =
    rank[result + 1](string l, API::Node s |
      s = pred.getASuccessor(l)
      or
      pred.refersTo(s) and l = ""
    |
      l + "->" + nodeRank(s)
    )
}

query predicate nodes(API::Node f, string key, string value) {
  key = "semmle.label" and
  value = f.toString()
  or
  key = "semmle.order" and
  value = nodeRank(f).toString()
}

query predicate edges(API::Node pred, API::Node succ, string key, string value) {
  exists(string lbl |
    succ = pred.getASuccessor(lbl)
    or
    pred.refersTo(succ) and
    lbl = ""
  |
    key = "semmle.label" and
    value = lbl
    or
    key = "semmle.order" and
    value = labelRank(pred, lbl, succ).toString()
  )
}
