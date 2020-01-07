/**
 * @name Useless assignment to property
 * @description An assignment to a property whose value is always overwritten has no effect.
 * @kind problem
 * @problem.severity warning
 * @id js/useless-assignment-to-property
 * @tags maintainability
 * @precision high
 */

import javascript
import Expressions.DOMProperties
import DeadStore

/**
 * Holds if `write`, which is the `i`th node of `bb`, writes to property `name` of `base`.
 *
 * We ignore writes to DOM properties and writes with an ambiguous base object.
 */
predicate propWrite(
  DataFlow::SourceNode base, string name, DataFlow::PropWrite write, ReachableBasicBlock bb, int i
) {
  write = base.getAPropertyWrite(name) and
  write.getWriteNode() = bb.getNode(i) and
  not isDOMProperty(name) and
  not exists(DataFlow::SourceNode otherBase |
    otherBase != base and
    write = otherBase.getAPropertyWrite(name)
  )
}

/**
 * Holds if there is a write to property `name` in container `sc`.
 */
predicate propWrittenInContainer(string name, StmtContainer sc) {
  exists(BasicBlock bb |
    propWrite(_, name, _, bb, _) and
    sc = bb.getContainer()
  )
}

/**
 * Holds if `e`, which is the `i`th node of `bb`, may read a property named `name`.
 *
 * We consider expressions with side effects to read all properties written in the same container.
 */
predicate propRead(BasicBlock bb, int i, Expr e, string name) {
  e = bb.getNode(i) and
  (
    e.(PropAccess).getPropertyName() = name and
    e instanceof RValue
    or
    // conservatively reject all side-effects
    e.isImpure() and
    propWrittenInContainer(name, bb.getContainer())
  )
}

/**
 * Gets the (zero-based) rank of the reference to property `name` at the `i`th node of `bb`
 * among all references to the same property in `bb`.
 */
int propRefRank(BasicBlock bb, int i, string name) {
  i = rank[result + 1](int j | propWrite(_, name, _, bb, j) or propRead(bb, j, _, name))
}

/**
 * Gets the maximum rank of a reference to property `name` in `bb`.
 */
int maxPropRefRank(BasicBlock bb, string name) { result = max(propRefRank(bb, _, name)) }

/**
 * Gets the (zero-based) rank of the write to property `name` of `base` at the `i`th node of `bb`
 * among all writes to property `name` of `base` in `bb`.
 */
int propWriteRank(DataFlow::SourceNode base, BasicBlock bb, int i, string name) {
  i = rank[result + 1](int j | propWrite(base, name, _, bb, j))
}

/**
 * Holds if `pw` is a write to property `name` on `base` whose rank among all references to
 * `name` in `base` is `rrnk`, and whose rank among all writes to property `name` of `base`
 * is `wrnk`.
 */
predicate rankedPropWrite(
  DataFlow::SourceNode base, string name, DataFlow::PropWrite pw, BasicBlock bb, int rrnk, int wrnk
) {
  exists(int i |
    propWrite(base, name, pw, bb, i) and
    rrnk = propRefRank(bb, i, name) and
    wrnk = propWriteRank(base, bb, i, name)
  )
}

/**
 * Holds if `pw1` and `pw2` are writes to property `name` on the same base object such
 * that `pw1` is the last reference to `name` in `bb1` and `pw2` is the first reference
 * to `name` in `bb2`, and `bb2` strictly post-dominates `bb1`.
 */
predicate postDominatingPropWrites(
  string name, DataFlow::PropWrite pw1, DataFlow::PropWrite pw2, ReachableBasicBlock bb1,
  ReachableBasicBlock bb2
) {
  exists(DataFlow::SourceNode base |
    rankedPropWrite(base, name, pw1, bb1, maxPropRefRank(bb1, name), _) and
    rankedPropWrite(base, name, pw2, bb2, 0, _) and
    bb2.strictlyPostDominates(bb1)
  )
}

/**
 * Gets a basic block that is between `bb1` and `bb2`, that is, it is reachable from `bb1` and
 * `bb2` is, in turn, reachable from it.
 *
 * We restrict `bb1` and `bb2` to be pairs of blocks containing post-dominating property
 * writes in the sense of the predicate `postDominatingPropWrites` above. Due to post-dominance,
 * we can compute the intermediate blocks by exploring the transitive successors of `bb1`,
 * stopping whenever we hit `bb2`.
 */
BasicBlock getAnIntermediateBlock(string name, BasicBlock bb1, BasicBlock bb2) {
  postDominatingPropWrites(name, _, _, bb1, bb2) and
  result = bb1
  or
  exists(BasicBlock bb |
    bb = getAnIntermediateBlock(name, bb1, bb2) and
    bb != bb2 and
    result = bb.getASuccessor()
  )
}

/**
 * Holds if property `name` is read in a basic block that is strictly between `bb1` and `bb2`.
 */
predicate propReadBetweenBlocks(string name, BasicBlock bb1, BasicBlock bb2) {
  exists(BasicBlock bb |
    bb = getAnIntermediateBlock(name, bb1, bb2) and
    bb != bb1 and
    bb != bb2 and
    propRead(bb, _, _, name)
  )
}

/**
 * Holds if `pw1` and `pw2` both assign property `name`, but `pw1` is dead because
 * `pw2` immediately overwrites the property.
 */
predicate isDeadAssignment(string name, DataFlow::PropWrite pw1, DataFlow::PropWrite pw2) {
  exists(DataFlow::SourceNode base, BasicBlock bb, int r, int w |
    rankedPropWrite(base, name, pw1, bb, r, w) and
    rankedPropWrite(base, name, pw2, bb, r+1, w+1)
  )
  or
  exists(BasicBlock bb1, BasicBlock bb2 |
    postDominatingPropWrites(name, pw1, pw2, bb1, bb2) and
    not propReadBetweenBlocks(name, bb1, bb2)
  )
}

from string name, DataFlow::PropWrite pw1, DataFlow::PropWrite pw2
where
  isDeadAssignment(name, pw1, pw2) and
  // whitelist
  not (
    // Google Closure Compiler pattern: `o.p = o['p'] = v`
    exists(PropAccess p1, PropAccess p2 |
      p1 = pw1.getAstNode() and
      p2 = pw2.getAstNode()
    |
      p1 instanceof DotExpr and p2 instanceof IndexExpr
      or
      p2 instanceof DotExpr and p1 instanceof IndexExpr
    )
    or
    // don't flag overwrites for default values
    isDefaultInit(pw1.getRhs().asExpr().getUnderlyingValue())
    or
    // don't flag assignments in externs
    pw1.getAstNode().inExternsFile()
    or
    // exclude result from js/overwritten-property
    pw2.getBase() instanceof DataFlow::ObjectLiteralNode
    or
    // exclude result from accessor declarations
    pw1.getWriteNode() instanceof AccessorMethodDeclaration
  ) and
  // exclude results from non-value definitions from `Object.defineProperty`
  (
    pw1 instanceof CallToObjectDefineProperty
    implies
    pw1.(CallToObjectDefineProperty).hasPropertyAttributeWrite("value", _)
  )
select pw1.getWriteNode(),
  "This write to property '" + name + "' is useless, since $@ always overrides it.",
  pw2.getWriteNode(), "another property write"
