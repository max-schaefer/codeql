import javascript

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

/**
 * Gets the maximum depth of a candidate representation.
 *
 * Increasing this bound will generate more candidate representations, but
 * will generally negatively affect performance. Note that rare candidates are
 * are filtered out above, so increasing the bound beyond a certain threshold may
 * not actually yield new candidates.
 */
int maxdepth() { result = 10 }

/** Gets a node that the main module of `pkgName` exports under the name `prop`. */
private DataFlow::Node getAnExport(string pkgName, string prop) {
  exists(NPMPackage pkg, Module m |
    pkg.getPackageName() = pkgName and
    m = pkg.getMainModule()
  |
    result = m.getAnExportedValue(prop)
    or
    exists(DataFlow::PropWrite pw |
      pw.writes(m.(NodeModule).getModuleVariable().getAnAccess().flow(), "exports", result) and
      prop = "default"
    )
  )
}

/**
 * Gets a representation of `nd` as a (suffix of an) access path, where that suffix has length
 *   `depth`.
 */
string rep(DataFlow::SourceNode nd, int depth) {
  // the global object
  isRelevant(nd) and
  nd = DataFlow::globalObjectRef() and
  result = "(global)" and
  depth = 1
  or
  // package imports/exports
  isRelevant(nd) and
  exists(string pkg |
    nd = DataFlow::moduleImport(pkg) and
    // avoid picking up local imports
    pkg.regexpMatch("[^./].*")
  |
    result = "(root https://www.npmjs.com/package/" + pkg + ")" and
    depth = 1
  )
  or
  // compound representations
  exists(DataFlow::SourceNode base, string step, string baserep |
    (
      baserep = rep(base, depth - 1) and
      // bound maximum depth of candidate representation
      depth <= maxdepth()
      or
      baserep = "*" and
      depth = 1 and
      // avoid creating trivial representations like `(return *)`
      step.regexpMatch("(member|parameter) [^\\d*].*") and
      isRelevant(nd)
    ) and
    result = "(" + step + " " + baserep + ")"
  |
    // members
    exists(DataFlow::PropRef prop |
      prop = base.getAPropertyRead() and
      nd = prop
    |
      step = "member " + prop.getPropertyName()
      or
      step = "member *"
    )
    or
    // instances
    (
      nd = base.getAnInstantiation()
      or
      nd = base.(DataFlow::ClassNode).getAnInstanceReference()
    ) and
    step = "instance"
    or
    // parameters
    exists(string p |
      exists(int i |
        nd = base.(DataFlow::FunctionNode).getParameter(i) and
        not exists(nd.(DataFlow::ParameterNode).getName())
      |
        p = i.toString()
      )
      or
      nd = base.(DataFlow::FunctionNode).getAParameter() and
      p = nd.(DataFlow::ParameterNode).getName()
    |
      step = "parameter " + p
    )
    or
    // return values
    nd = base.getACall() and
    step = "return"
    or
    // await
    base.flowsToExpr(nd.asExpr().(AwaitExpr).getOperand()) and
    step = "await"
  )
  or
  // global variables, which are treated as members of the global object
  isRelevant(nd) and
  exists(string g | nd = DataFlow::globalVarRef(g) |
    result = "(member " + g + " (global))" and
    depth = 2
  )
}

string rep(DataFlow::SourceNode nd) { result = rep(nd, _) }

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

from DataFlow::SourceNode base, string prop, DataFlow::PropRef propref, boolean isDereferenced
where
  propref = base.getAPropertyReference(prop) and
  (if isDereferenced(propref) then isDereferenced = true else isDereferenced = false)
select propref, rep(base), prop, isDereferenced
