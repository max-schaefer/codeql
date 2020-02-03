/**
 * @name Portal-based jump-to-definition links
 * @description Compares an implementation of jump-to-definition based on portals to
 *              the standard version.
 * @kind table
 * @id js/portal-based-jump-to-def
 */

import javascript
import definitions
import semmle.javascript.dataflow.Portals

Expr use(Portal p) {
  exists(DataFlow::Node x | x = p.getAnExitNode(_) |
    if x instanceof DataFlow::PropRead
    then result = x.(DataFlow::PropRead).getPropertyNameExpr()
    else
      if x = any(Import i).getImportedModuleNode()
      then result = any(Import i | i.getImportedModuleNode() = x).getImportedPath()
      else result = x.getAstNode()
  )
}

ASTNode def(Portal p) {
  if p instanceof NpmPackagePortal
  then result = NpmPackagePortal::packageMain(p.(NpmPackagePortal).getName())
  else
    exists(DataFlow::Node e | e = p.getAnEntryNode(_) |
      if e = any(DataFlow::PropWrite pw).getRhs()
      then result = any(DataFlow::PropWrite pw | pw.getRhs() = e).getAstNode()
      else result = e.getAstNode()
    )
}

string pploc(Location l) {
  result = l.getFile() + ":" + l.getStartLine() + ":" + l.getStartColumn()
}

NPMPackage package(File f) { result.getAFile() = f }

predicate expected(Locatable ref, Locatable decl) {
  (
    variableDefLookup(ref, decl, _)
    or
    // prefer definitions over declarations
    not variableDefLookup(ref, _, _) and
    variableDeclLookup(ref, decl, _)
    or
    importLookup(ref, decl, _)
    or
    propertyLookup(ref, decl, _)
  ) and
  // portals can't help with global variables
  not ref instanceof GlobalVarAccess and
  // ignore externs
  not ref.(ASTNode).inExternsFile() and
  not decl.(ASTNode).inExternsFile() and
  // concentrate on cross-package references
  exists(package(ref.getFile())) and
  exists(package(decl.getFile())) and
  not package(ref.getFile()) = package(decl.getFile())
}

predicate actual(Locatable ref, Locatable decl) {
  exists(Portal p |
    ref = use(p) and
    decl = def(p)
  )
}

from Locatable ref, Locatable decl, string kind
where
  expected(ref, decl) and not actual(ref, decl) and kind = "missing"
  or
  not expected(ref, decl) and actual(ref, decl) and kind = "unexpected"
select kind, ref, pploc(ref.getLocation()), decl, pploc(decl.getLocation())
