/** Provides classes for working with `node-pre-gyp`. */

import javascript

/** A call to the `find` function from module `node-pre-gyp`. */
class NodePreGypFindCall extends DataFlow::CallNode {
  NodePreGypFindCall() { this = DataFlow::moduleImport("node-pre-gyp").getAMemberCall("find") }

  private PathExpr getPath() { result = getArgument(0).asExpr() }

  private PackageJSON getPackageJson() { result.getFile() = getPath().resolve() }

  string getNativeModuleName() {
    result = getPackageJson().getPropValue("binary").(JSONObject).getPropStringValue("module_name")
  }
}

/** The first argument to `node-pre-gyp.find`, considered as a path expression. */
private class NodePreGypPath extends PathExprCandidate {
  NodePreGypPath() { this = any(NodePreGypFindCall npgfc).getArgument(0).asExpr() }
}

/** A constant path-expression part in a call to `node-pre-gyp.find`. */
private class ConstantNodePreGypPathElement extends PathExpr, ConstantString {
  ConstantNodePreGypPathElement() { this = any(NodePreGypPath npgp).getAPart() }

  override string getValue() { result = getStringValue() }
}
