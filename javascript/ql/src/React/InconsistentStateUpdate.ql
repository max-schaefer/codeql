/**
 * @name Potentially inconsistent state update
 * @description Updating the state of a component based on the current value of
 *              'this.state' or 'this.props' may lead to inconsistent component
 *              state.
 * @kind problem
 * @problem.severity warning
 * @id js/react/inconsistent-state-update
 * @tags reliability
 *       frameworks/react
 * @precision very-high
 */

import semmle.javascript.frameworks.React

/**
 * Gets an unsafe property access, that is, an expression that reads (a property of)
 * `this.state` or `this.prop` on component `c`.
 */
DataFlow::PropRead getAnUnsafeAccess(ReactComponent c) {
  result = c.getAPropRead() or
  result = c.getAStateAccess()
}

/**
 * Gets at unsafe property access that is not the base of another unsafe property
 * access.
 */
DataFlow::PropRead getAnOutermostUnsafeAccess(ReactComponent c) {
  result = getAnUnsafeAccess(c) and
  not exists(DataFlow::PropRead outer | outer = getAnUnsafeAccess(c) | result = outer.getBase())
}

/**
 * Gets a property write through `setState` for state property `name` of `c` in container `sc`.
 */
DataFlow::PropWrite getAStateUpdate(ReactComponent c, string name, StmtContainer sc) {
  exists(DataFlow::ObjectLiteralNode newState |
    newState.flowsTo(c.getAMethodCall("setState").getArgument(0)) and
    result = newState.getAPropertyWrite(name) and
    sc = result.getContainer()
  )
}

/**
 * Gets a property write through `setState` for a state property of `c` that is only written at this property write.
 */
DataFlow::PropWrite getAUniqueStateUpdate(ReactComponent c) {
  exists(string name |
    count(getAStateUpdate(c, name, _)) = 1 and
    result = getAStateUpdate(c, name, _)
  )
}

/**
 * Gets a property read of state property `name` of `c` in container `sc`.
 */
DataFlow::PropRead getAStateRead(ReactComponent c, string name, StmtContainer sc) {
  c.getADirectStateAccess().flowsTo(result.getBase()) and
  result.getPropertyName() = name and
  sc = result.getContainer()
}

/**
 * Holds if `e` is syntactically nested inside the right-hand side of property write `pwn`.
 */
predicate inStateUpdateRhs(DataFlow::PropWrite pwn, Expr e) {
  pwn = getAStateUpdate(_, _, _) and
  e = pwn.getRhs().asExpr()
  or
  inStateUpdateRhs(pwn, e.getParentExpr())
}

/**
 * Holds for "self dependent" component state updates. E.g. `this.setState({toggled: !this.state.toggled})`.
 */
predicate isAStateUpdateFromSelf(ReactComponent c, DataFlow::PropWrite pwn, DataFlow::PropRead prn) {
  exists(string name, StmtContainer sc |
    pwn = getAStateUpdate(c, name, sc) and
    prn = getAStateRead(c, name, sc) and
    inStateUpdateRhs(pwn, prn.asExpr())
  )
}

/**
 * Holds if `getState` is an outermost unsafe property access on `c` in `enclosingFn`.
 */
predicate getState(ReactComponent c, Expr getState, Function enclosingFn) {
  getState = getAnOutermostUnsafeAccess(c).asExpr() and
  enclosingFn = getState.getEnclosingFunction()
}

/**
 * Holds if `setState` is a call to `setState` on `c` in `enclosingFn`.
 */
predicate setStateCall(ReactComponent c, MethodCallExpr setState, Function enclosingFn) {
  setState = c.getAMethodCall("setState").asExpr() and
  enclosingFn = setState.getEnclosingFunction()
}

/**
 * Holds if `e` is syntactically nested within the first argument of a `setState` call.
 */
predicate inFirstArgToSetState(MethodCallExpr setState, Expr e) {
  setStateCall(_, setState, _) and
  e = setState.getArgument(0)
  or
  inFirstArgToSetState(setState, e.getParentExpr())
}

from ReactComponent c, MethodCallExpr setState, Expr getState, Function f
where
  getState(c, getState, f) and
  setStateCall(c, setState, f) and
  inFirstArgToSetState(setState, getState) and
  // ignore self-updates that only occur in one location: `setState({toggled: !this.state.toggled})`, they are most likely safe in practice
  not exists(DataFlow::PropWrite pwn |
    pwn = getAUniqueStateUpdate(c) and
    isAStateUpdateFromSelf(c, pwn, DataFlow::valueNode(getState))
  )
select setState, "Component state update uses $@.", getState, "potentially inconsistent value"
