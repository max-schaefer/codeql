/**
 * @kind table
 */

import javascript

/**
 * Holds if `propref` is dereferenced, that is, if the property does not exist, then the program
 * will throw an exception or perform possibly unexpected coercions.
 */
predicate isDereferenced(DataFlow::PropRef propref) {
  propref instanceof DataFlow::PropWrite
  or
  exists(DataFlow::PropRead pr | pr = propref |
    exists(pr.getAnInvocation())
    or
    exists(pr.getAPropertyReference())
    or
    exists(ForOfStmt f | pr.flowsToExpr(f.getIterationDomain()))
    or
    exists(BinaryExpr be | not be instanceof EqualityTest | pr.flowsToExpr(be.getAnOperand()))
    or
    exists(UnaryExpr ue |
      not ue instanceof LogNotExpr and
      not ue instanceof TypeofExpr and
      not ue instanceof VoidExpr and
      not ue instanceof DeleteExpr
    |
      pr.flowsToExpr(ue.getOperand())
    )
    or
    exists(UpdateExpr ue | pr.flowsToExpr(ue.getOperand()))
  )
}

/**
 * Gets the number of arguments `pr` is invoked with, if any.
 */
int getNumArgs(DataFlow::PropRead pr) { result = pr.getAnInvocation().getNumArgument() }

/**
 * Gets the number of arguments `pr` is invoked with, if any, and otherwise `-1`.
 */
int getNumArgsOpt(DataFlow::PropRef pr) {
  if exists(getNumArgs(pr)) then result = getNumArgs(pr) else result = -1
}

/**
 * Holds if `nd` is relevant to program semantics.
 */
predicate isRelevant(DataFlow::Node nd) {
  // exclude externs files (i.e., our manually-written API models) and ambient files (such as
  // TypeScript `.d.ts` files); there is no real data flow going on in those
  not nd.getTopLevel().isExterns() and
  not nd.getTopLevel().isAmbient() and
  nd.getBasicBlock() instanceof ReachableBasicBlock
}

from API::Node base, string prop, DataFlow::PropRef propref, boolean isDereferenced
where
  propref.getBase() = base.getAUse() and
  propref.getPropertyName() = prop and
  (if isDereferenced(propref) then isDereferenced = true else isDereferenced = false) and
  isRelevant(propref)
select propref, base.toString() as ap, prop, isDereferenced, getNumArgsOpt(propref) as numArgs
