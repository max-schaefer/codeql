/**
 * Provides an implementation of  _API graphs_, which are an abstract representation of the API
 * surface of an NPM package.
 *
 * Modules are identified by a _module specifier_, which may take any of the following forms:
 *   1. `builtin:m`: the Node.js built-in module `m`
 *   2. `native:m`: the native module with name `m`
 *   3. `npm:pkg`: the main module of npm package `pkg`
 */

import javascript
import NodePreGyp

module ApiGraph {
  module Label {
    /** Gets the edge label for the module with spec `s`. */
    bindingset[result]
    bindingset[s]
    string mod(string s) { result = "module " + s }

    private predicate isMemberName(string m) {
      m = any(DataFlow::PropRef pr).getPropertyName() or
      any(AnalyzedPropertyWrite apw).writes(_, m, _) or
      m = any(CanonicalName cn).getName() or
      exists(any(DataFlow::ClassNode cn).getInstanceMethod(m)) or
      m = "default" or
      RemoteApiGraph::edge(_, _, "member " + m)
    }

    /** Gets the `member` edge label for member `m`. */
    string member(string m) {
      result = "member " + m and
      isMemberName(m) and
      // only consider alpha-numeric properties, excluding special properties
      // and properties whose names look like they are meant to be internal
      m.regexpMatch("(?!prototype$|__)[a-zA-Z_][\\w\\-.]*")
    }

    /** Gets the `member` edge label for the unknown member. */
    string unknownMember() { result = "member *" }

    /** Gets the `instance` edge label. */
    string instance() { result = "instance" }

    private int maxParm() {
      result =
        max(int n |
          exists(any(DataFlow::CallNode c).getArgument(n)) or
          exists(any(DataFlow::FunctionNode fn).getParameter(n))
        )
    }

    /** Gets the `parameter` edge label for the `i`th parameter. */
    string parameter(int i) {
      result = "parameter " + i and i in [0 .. maxParm()]
      or
      exists(string p |
        RemoteApiGraph::edge(_, _, result) and
        result = "parameter " + p and
        i = p.toInt()
      )
    }

    /** Gets the `parameter` edge label for the receiver. */
    string receiver() { result = "parameter -1" }

    /** Gets the `return` edge label. */
    string return() { result = "return" }

    /** Gets the `promise` edge label connecting a promise to its contained value. */
    string promise() { result = "promise" }
  }
}

module LocalApiGraph {
  import ApiGraph

  cached
  private module Impl {
    /** Holds if `m` is the name of a Node.js built-in module. */
    private predicate isNodeBuiltinModuleName(string m) {
      m = "assert" or
      m = "async_hooks" or
      m = "buffer" or
      m = "child_process" or
      m = "cluster" or
      m = "console" or
      m = "constants" or
      m = "crypto" or
      m = "dgram" or
      m = "dns" or
      m = "domain" or
      m = "events" or
      m = "fs" or
      m = "http2" or
      m = "http" or
      m = "https" or
      m = "inspector" or
      m = "module" or
      m = "net" or
      m = "os" or
      m = "path" or
      m = "perf_hooks" or
      m = "process" or
      m = "punycode" or
      m = "querystring" or
      m = "readline" or
      m = "repl" or
      m = "stream" or
      m = "string_decoder" or
      m = "sys" or
      m = "timers" or
      m = "tls" or
      m = "trace_events" or
      m = "tty" or
      m = "url" or
      m = "util" or
      m = "v8" or
      m = "vm" or
      m = "worker_threads" or
      m = "zlib"
    }

    /**
     * Holds if `mod` is the implementation of the Node.js built-in module `m`.
     *
     * This is currently implemented heuristically.
     */
    private predicate isNodeBuiltinModule(Module mod, string m) {
      isNodeBuiltinModuleName(m) and
      mod.getFile().getRelativePath().regexpMatch("(.*/)?lib/" + m + ".js")
    }

    /** Holds if `imp` is an import of the module specified by `spec`. */
    private predicate imports(DataFlow::SourceNode imp, string spec) {
      exists(string path |
        imp = DataFlow::moduleImport(path) and
        // path must not start with a dot or a slash
        path.regexpMatch("[^./].*") and
        if isNodeBuiltinModuleName(path) then spec = "builtin:" + path else spec = "npm:" + path
      )
      or
      exists(Require req, NodePreGypFindCall npgfc |
        req.getArgument(0).flow().getALocalSource() = npgfc
      |
        imp = req.flow() and
        spec = "native:" + npgfc.getNativeModuleName()
      )
    }

    /** Gets a module with the given `spec`. */
    private Module importableModule(string spec) {
      exists(NPMPackage pkg, PackageJSON json |
        json = pkg.getPackageJSON() and not json.isPrivate()
      |
        result = pkg.getMainModule() and
        spec = "npm:" + pkg.getPackageName()
      )
      or
      exists(string m |
        spec = "builtin:" + m and
        isNodeBuiltinModule(result, m)
      )
    }

    /** Holds if a module with the given `spec` exports `exp`. */
    private predicate exports(string spec, DataFlow::Node exp) {
      exists(Module m | m = importableModule(spec) |
        exists(AnalyzedPropertyWrite apw |
          apw.writes(m.(AnalyzedModule).getModuleObject(), "exports", exp)
        )
        or
        m.(ES2015Module).exports("default", exp.(DataFlow::ValueNode).getAstNode())
      )
    }

    /** Holds if a module with the given `spec` exports `rhs` under the name `prop`. */
    private predicate exports(string spec, string prop, DataFlow::Node rhs) {
      exists(AnalyzedModule m, DefiniteAbstractValue exp |
        m = importableModule(spec) and exp = m.getAnExportsValue()
      |
        exists(AnalyzedPropertyWrite apw | apw.writes(exp, prop, rhs))
        or
        // mostly overlaps with the above, but handles cases where the exported property isn't read
        // anywhere in the code base
        exists(DataFlow::PropWrite pw, DataFlow::Node exports |
          exports.analyze().getAValue() = exp and
          pw.writes(exports, prop, rhs)
        )
      )
      or
      exports(spec, rhs) and
      prop = "default"
    }

    cached
    newtype TNode =
      MkRootNode() or
      MkSyntheticExportNode(string modSpec) { exports(modSpec, _, _) } or
      MkSyntheticInstanceNode(DataFlow::ClassNode cls) { cls = trackDefNode(_) } or
      MkDefNode(DataFlow::Node nd) {
        not nd.getTopLevel().isExterns() and
        (
          nd = root2Def(_) or
          nd = def2Def(_, _) or
          nd = instance2Def(_, _) or
          nd = export2Def(_, _) or
          nd = use2Def(_, _) or
          nd = any(DataFlow::FunctionNode f | exists(MkAsyncFuncResult(f))).getAReturn()
        )
      } or
      MkUseNode(DataFlow::SourceNode nd) {
        not nd.getTopLevel().isExterns() and
        (
          nd = root2Use(_) or
          nd = use2Use(_, _) or
          nd = def2Use(_, _) or
          nd = getANodeWithType(_) or
          nd
              .(AnalyzedPropertyRead)
              .reads(importableModule(_).(NodeModule).getAModuleExportsValue(), _)
        )
      } or
      MkForwardedNode(RemoteApiGraph::Node nd) {
        exists(DefNode def, RemoteApiGraph::Node rem |
          edge(def, "", rem.getLocalNode()) and
          nd = rem.getASuccessor(_)
        )
        or
        exists(MkForwardedNode(nd.getAPredecessor(_)))
      } or
      MkTypeScriptDefNode(CanonicalName n) { isDefined(n) } or
      MkTypeScriptUseNode(CanonicalName n) { isUsed(n) } or
      MkAsyncFuncResult(DataFlow::FunctionNode f) {
        f = trackDefNode(_) and f.getFunction().isAsync()
      }

    private predicate isUsed(CanonicalName n) {
      exists(n.(TypeName).getAnAccess()) or
      exists(n.(Namespace).getAnAccess()) or
      exists(InvokeExpr invk | ast_node_symbol(invk, n))
    }

    private predicate isDefined(CanonicalName n) {
      exists(ASTNode def |
        def = n.(TypeName).getADefinition() or
        def = n.(Namespace).getADefinition() or
        def = n.(CanonicalFunctionName).getADefinition()
      |
        not def.isAmbient()
      )
    }

    private DataFlow::Node root2Def(string lbl) {
      exists(string spec |
        lbl = Label::mod(spec) and
        exports(spec, result)
      )
    }

    private DataFlow::Node root2Use(string lbl) {
      exists(string spec |
        lbl = Label::mod(spec) and
        imports(result, spec)
      )
    }

    private DataFlow::SourceNode trackUseNode(DataFlow::SourceNode nd, DataFlow::TypeTracker t) {
      t.start() and
      exists(MkUseNode(nd)) and
      result = nd
      or
      exists(DataFlow::TypeTracker t2 | result = trackUseNode(nd, t2).track(t2, t))
    }

    cached
    DataFlow::SourceNode trackUseNode(DataFlow::SourceNode nd) {
      result = trackUseNode(nd, DataFlow::TypeTracker::end())
    }

    private DataFlow::SourceNode use2Use(DataFlow::SourceNode pred, string lbl) {
      exists(DataFlow::PropRead pr | pr = trackUseNode(pred).getAPropertyRead() and result = pr |
        lbl = Label::member(pr.getPropertyName())
        or
        not exists(pr.getPropertyName()) and
        lbl = Label::unknownMember()
      )
      or
      lbl = Label::instance() and
      result = trackUseNode(pred).getAnInstantiation()
      or
      lbl = Label::return() and
      result = trackUseNode(pred).getAnInvocation()
      or
      lbl = Label::promise() and
      trackUseNode(pred).flowsToExpr(result.asExpr().(AwaitExpr).getOperand())
      or
      lbl = Label::promise() and
      result = trackUseNode(pred).getAMethodCall("then").getCallback(0).getParameter(0)
    }

    private DataFlow::SourceNode trackDefNode(DataFlow::Node nd, DataFlow::TypeBackTracker t) {
      t.start() and
      exists(MkDefNode(nd)) and
      result = nd.getALocalSource()
      or
      exists(DataFlow::TypeBackTracker t2 | result = trackDefNode(nd, t2).backtrack(t2, t))
    }

    cached
    DataFlow::SourceNode trackDefNode(DataFlow::Node nd) {
      result = trackDefNode(nd, DataFlow::TypeBackTracker::end())
    }

    private DataFlow::Node def2Def(DataFlow::Node pred, string lbl) {
      exists(DataFlow::SourceNode predOrigin | predOrigin = trackDefNode(pred) |
        exists(DataFlow::PropWrite pw |
          pw = predOrigin.getAPropertyWrite() and result = pw.getRhs()
        |
          lbl = Label::member(pw.getPropertyName())
          or
          not exists(pw.getPropertyName()) and
          lbl = Label::unknownMember()
        )
        or
        exists(DataFlow::FunctionNode fn | fn = predOrigin |
          not fn.getFunction().isAsync() and
          lbl = Label::return() and
          result = fn.getAReturn()
        )
        or
        lbl = Label::promise() and
        result = predOrigin.(PromiseDefinition).getResolveParameter().getACall().getArgument(0)
        or
        lbl = Label::promise() and
        result = predOrigin.(PromiseCreationCall).getValue() and
        not predOrigin instanceof PromiseAllCreation
        or
        lbl = Label::promise() and
        exists(DataFlow::MethodCallNode m | m = predOrigin |
          m.getMethodName() = "then" and
          result = m.getCallback([0 .. 1]).getAReturn()
        )
      )
      or
      exists(DataFlow::ClassNode cls, string name |
        exists(MkDefNode(pred)) and
        cls.getAnInstanceReference().flowsTo(pred) and
        lbl = Label::member(name) and
        result = cls.getInstanceMethod(name)
      )
    }

    private DataFlow::Node instance2Def(DataFlow::ClassNode cls, string lbl) {
      exists(string name |
        exists(MkSyntheticInstanceNode(cls)) and
        lbl = Label::member(name) and
        result = cls.getInstanceMethod(name)
      )
    }

    private DataFlow::ClassNode def2Instance(DataFlow::Node base, string lbl) {
      lbl = Label::instance() and
      result = trackDefNode(base)
    }

    private DataFlow::Node export2Def(string spec, string lbl) {
      exists(string prop |
        lbl = Label::member(prop) and
        exports(spec, prop, result)
      )
    }

    private DataFlow::Node use2Def(DataFlow::SourceNode nd, string lbl) {
      exists(DataFlow::InvokeNode invk | invk = trackUseNode(nd).getAnInvocation() |
        exists(int i |
          lbl = Label::parameter(i) and
          result = invk.getArgument(i)
        )
        or
        lbl = Label::receiver() and
        result = invk.(DataFlow::CallNode).getReceiver()
      )
      or
      exists(DataFlow::PropWrite pw |
        pw = trackUseNode(nd).getAPropertyWrite() and result = pw.getRhs()
      |
        lbl = Label::member(pw.getPropertyName())
        or
        not exists(pw.getPropertyName()) and
        lbl = Label::unknownMember()
      )
    }

    private DataFlow::Node def2Use(DataFlow::Node nd, string lbl) {
      exists(DataFlow::FunctionNode fn | fn = trackDefNode(nd) |
        exists(int i |
          lbl = Label::parameter(i) and
          result = fn.getParameter(i)
        )
        or
        lbl = Label::receiver() and
        result = fn.getReceiver()
      )
      or
      exists(DataFlow::ClassNode cls, int i | cls = trackDefNode(nd) |
        lbl = Label::parameter(i) and
        result = cls.getConstructor().getParameter(i)
      )
      or
      exists(DataFlow::ClassNode cls |
        exists(MkDefNode(nd)) and
        lbl = Label::instance() and
        cls.getAClassReference().flowsTo(nd) and
        result = cls.getAReceiverNode()
      )
    }

    private DataFlow::SourceNode getANodeWithType(TypeName tn) {
      exists(string moduleName, string typeName |
        tn.hasQualifiedName(moduleName, typeName) and
        result.hasUnderlyingType(moduleName, typeName)
      )
    }

    /**
     * Holds if there is an edge from `pred` to `succ` in the API graph that is labeled with `lbl`.
     */
    cached
    predicate edge(TNode pred, string lbl, TNode succ) {
      // `module` edge
      pred = MkRootNode() and
      succ = MkDefNode(root2Def(lbl))
      or
      exists(string spec | lbl = Label::mod(spec) |
        pred = MkRootNode() and
        succ = MkSyntheticExportNode(spec)
      )
      or
      pred = MkRootNode() and
      succ = MkUseNode(root2Use(lbl))
      or
      exists(DataFlow::SourceNode base |
        pred = MkUseNode(base) and
        succ = MkUseNode(use2Use(base, lbl))
      )
      or
      exists(DataFlow::Node nd |
        pred = MkDefNode(nd) and
        succ = MkDefNode(def2Def(nd, lbl))
      )
      or
      exists(DataFlow::SourceNode ctor |
        pred = MkSyntheticInstanceNode(ctor) and
        succ = MkDefNode(instance2Def(ctor, lbl))
      )
      or
      exists(string spec | pred = MkSyntheticExportNode(spec) |
        succ = MkDefNode(export2Def(spec, lbl))
        or
        exists(NodeModule m, AnalyzedPropertyRead pr, string prop |
          m = importableModule(spec) and
          pr.reads(m.getAModuleExportsValue(), prop) and
          lbl = Label::member(prop) and
          succ = MkUseNode(pr)
        )
      )
      or
      exists(DataFlow::Node base |
        pred = MkDefNode(base) and
        succ = MkSyntheticInstanceNode(def2Instance(base, lbl))
      )
      or
      exists(DataFlow::SourceNode fn |
        pred = MkUseNode(fn) and
        succ = MkDefNode(use2Def(fn, lbl))
      )
      or
      exists(DataFlow::Node nd |
        pred = MkDefNode(nd) and
        succ = MkUseNode(def2Use(nd, lbl))
      )
      or
      exists(DataFlow::Node def, DataFlow::Node use |
        pred = MkDefNode(def) and
        succ = MkUseNode(use) and
        trackUseNode(use).flowsTo(def) and
        lbl = ""
      )
      or
      exists(RemoteApiGraph::Node rem |
        edge(pred, "", rem.getLocalNode()) and
        succ = MkForwardedNode(rem.getASuccessor(lbl))
      )
      or
      exists(RemoteApiGraph::Node rem |
        pred = MkForwardedNode(rem) and
        succ = MkForwardedNode(rem.getASuccessor(lbl))
      )
      or
      exists(CanonicalName cn |
        pred = MkRootNode() and
        lbl = Label::mod("npm:" + cn.getExternalModuleName())
      |
        succ = MkTypeScriptUseNode(cn) or
        succ = MkTypeScriptDefNode(cn)
      )
      or
      exists(CanonicalName cn1, CanonicalName cn2 |
        cn2 = cn1.getAChild() and
        lbl = Label::member(cn2.getName())
      |
        (pred = MkTypeScriptDefNode(cn1) or pred = MkTypeScriptUseNode(cn1)) and
        (succ = MkTypeScriptDefNode(cn2) or succ = MkTypeScriptUseNode(cn2))
      )
      or
      exists(TypeName tn |
        pred = MkTypeScriptUseNode(tn) and
        lbl = Label::instance() and
        succ = MkUseNode(getANodeWithType(tn))
      )
      or
      exists(DataFlow::Node nd, DataFlow::FunctionNode f |
        pred = MkDefNode(nd) and
        f = trackDefNode(nd) and
        lbl = Label::return() and
        succ = MkAsyncFuncResult(f)
      )
      or
      exists(DataFlow::FunctionNode f |
        pred = MkAsyncFuncResult(f) and
        lbl = Label::promise() and
        succ = MkDefNode(f.getAReturn())
      )
    }

    /** Holds if there is a non-alias edge from `pred` to `succ` in the API graph. */
    cached
    predicate edge(TNode pred, TNode succ) {
      exists(string lbl | edge(pred, lbl, succ) and lbl != "")
    }

    /** Gets the shortest distance from the root node to `nd` in the API graph. */
    cached
    int distanceFromRoot(TNode nd) = shortestDistances(MkRootNode/0, edge/2)(_, nd, result)
  }

  /**
   * An API node, that is, an abstract representation of an API component.
   */
  class Node extends Impl::TNode {
    predicate hasLocationInfo(string path, int startline, int startcol, int endline, int endcol) {
      (
        this instanceof Impl::MkRootNode or
        this instanceof Impl::MkSyntheticExportNode or
        this instanceof Impl::MkForwardedNode or
        this instanceof Impl::MkTypeScriptDefNode or
        this instanceof Impl::MkTypeScriptUseNode
      ) and
      path = "" and
      startline = 0 and
      startcol = 0 and
      endline = 0 and
      endcol = 0
      or
      exists(DataFlow::Node ctor | this = Impl::MkSyntheticInstanceNode(ctor) |
        ctor.hasLocationInfo(path, startline, startcol, _, _) and
        endline = startline and
        endcol = startcol
      )
      or
      exists(DataFlow::Node nd | this = Impl::MkDefNode(nd) or this = Impl::MkUseNode(nd) |
        nd.hasLocationInfo(path, startline, startcol, endline, endcol)
      )
      or
      exists(DataFlow::FunctionNode f | this = Impl::MkAsyncFuncResult(f) |
        startline = endline and
        startcol = endcol and
        f.hasLocationInfo(path, _, _, endline, endcol)
      )
    }

    string toString() {
      this instanceof RootNode and result = "root"
      or
      result = "def " + this.(DefNode).getPath()
      or
      result = "use " + this.(UseNode).getPath()
    }

    Node getAPredecessor(string lbl) {
      Impl::edge(result, lbl, this) and
      lbl != ""
      or
      exists(Node mid | Impl::edge(mid, "", this) | result = mid.getAPredecessor(lbl))
    }

    Node getASuccessor(string lbl) { this = result.getAPredecessor(lbl) }

    Node getAPredecessor() { result = getAPredecessor(_) }

    Node getASuccessor() { result = getASuccessor(_) }

    Node getARawSuccessor(string lbl) { Impl::edge(this, lbl, result) }

    bindingset[m]
    bindingset[result]
    Node getModule(string m) { result = getASuccessor(Label::mod(m)) }

    Node getMember(string m) { result = getASuccessor(Label::member(m)) }

    Node getUnknownMember() { result = getASuccessor(Label::unknownMember()) }

    Node getAMember() {
      result = getASuccessor(Label::member(_)) or
      result = getUnknownMember()
    }

    Node getInstance() { result = getASuccessor(Label::instance()) }

    Node getParameter(int i) { result = getASuccessor(Label::parameter(i)) }

    int getNumParameter() { result = max(int i | exists(getParameter(i))) + 1 }

    Node getLastParameter() { result = getParameter(getNumParameter() - 1) }

    Node getReceiver() { result = getASuccessor(Label::receiver()) }

    Node getAParameter() { result = getParameter(_) or result = getReceiver() }

    Node getResult() { result = getASuccessor(Label::return()) }

    Node getPromised() { result = getASuccessor(Label::promise()) }

    private string getAPath(int length) {
      this instanceof Impl::MkRootNode and
      length = 0 and
      result = ""
      or
      exists(Node pred, string lbl, string predpath |
        Impl::edge(pred, lbl, this) and
        lbl != "" and
        predpath = pred.getAPath(length - 1) and
        exists(string space | if length = 1 then space = "" else space = " " |
          result = "(" + lbl + space + predpath + ")" and
          // avoid producing strings longer than 1MB
          result.length() < 1000 * 1000
        )
      ) and
      length in [1 .. Impl::distanceFromRoot(this)]
    }

    /**
     * Gets a string representation of the lexicographically least among all shortest paths
     * from the root to this node.
     */
    string getPath() { result = min(string p | p = getAPath(Impl::distanceFromRoot(this)) | p) }

    int getKind() { result = -1 }

    /**
     * Gets a data-flow node corresponding to a use of this API component.
     */
    DataFlow::Node getAUse() {
      exists(DataFlow::SourceNode src | this = Impl::MkUseNode(src) | src.flowsTo(result))
      or
      exists(CanonicalName n | this = Impl::MkTypeScriptUseNode(n) |
        result = DataFlow::valueNode(n.getAnAccess())
      )
    }

    /**
     * Gets a data-flow node corresponding to the right-hand side of a definition of this API
     * component.
     */
    DataFlow::Node getADefinition() {
      this = Impl::MkDefNode(result)
      or
      exists(CanonicalName n | this = Impl::MkTypeScriptDefNode(n) |
        result = n.(Namespace).getADefinition().flow() or
        result = n.(CanonicalFunctionName).getADefinition().flow()
      )
    }
  }

  class RootNode extends Node, Impl::MkRootNode {
    override int getKind() { result = 0 }
  }

  /**
   * An definition node, that is, a node where an API component is defined.
   */
  class DefNode extends Node {
    DefNode() {
      this instanceof Impl::MkDefNode or
      this instanceof Impl::MkSyntheticExportNode or
      this instanceof Impl::MkSyntheticInstanceNode or
      this = Impl::MkForwardedNode(any(RemoteApiGraph::DefNode remdef)) or
      this instanceof Impl::MkTypeScriptDefNode or
      this instanceof Impl::MkAsyncFuncResult
    }

    override int getKind() { result = 1 }
  }

  /**
   * A use node, that is, a node where an API component is used.
   */
  class UseNode extends Node {
    UseNode() {
      this instanceof Impl::MkUseNode or
      this = Impl::MkForwardedNode(any(RemoteApiGraph::UseNode remuse)) or
      this instanceof Impl::MkTypeScriptUseNode
    }

    override int getKind() { result = 2 }
  }

  RootNode root() { any() }

  bindingset[m]
  UseNode moduleImport(string m) { result = root().getModule(m) }

  bindingset[m]
  bindingset[result]
  DefNode moduleDefinition(string m) { result = root().getModule(m) }

  Node forwardNode(RemoteApiGraph::Node nd) { result = Impl::MkForwardedNode(nd) }
}

module RemoteApiGraph {
  import ApiGraph
  private import external.ExternalArtifact

  private predicate node(string path, int kind) {
    exists(ExternalData e | e.getDataPath() = "ApiGraphNodes.csv" |
      e.getField(0) = path and
      e.getField(1) = "kind" and
      e.getFieldAsInt(2) = kind
    )
  }

  predicate edge(string pred, string succ, string value) {
    exists(ExternalData e | e.getDataPath() = "ApiGraphEdges.csv" |
      e.getField(0) = pred and
      e.getField(1) = succ and
      e.getField(2) = "semmle.label" and
      e.getField(3) = value
    )
  }

  private predicate edge(string pred, string succ) { edge(pred, succ, _) }

  private newtype TNode =
    MkRootNode(string path) { node(path, 0) } or
    MkDefNode(string path) { node(path, 1) } or
    MkUseNode(string path) { node(path, 2) }

  private predicate isRelevant(string path) {
    exists(ExternalData e |
      e.getField(0).matches("%Summary") and
      path = e.getField(_)
    )
    or
    edge(path, any(string path2 | isRelevant(path2)))
  }

  class Node extends TNode {
    string path;

    Node() {
      (this = MkRootNode(path) or this = MkDefNode(path) or this = MkUseNode(path)) and
      isRelevant(path)
    }

    Node getAPredecessor(string lbl) {
      edge(result.getPath(), this.getPath(), lbl) and
      lbl != ""
      or
      exists(Node mid | edge(mid.getPath(), this.getPath(), "") | result = mid.getAPredecessor(lbl))
    }

    Node getASuccessor(string lbl) { this = result.getAPredecessor(lbl) }

    /**
     * Gets a string representation of the lexicographically least among all shortest paths
     * from the root to this node.
     */
    string getPath() { result = path }

    cached
    LocalApiGraph::Node getLocalNode() {
      match(this, result)
      or
      // we allow a certain amount of imprecise matching: if `rem` matches `loc`
      // precisely, then we also want to match `rem.p` against `loc[e]`, and potentially
      // one step more (e.g., `rem.p()` matches `loc[e]()`); matching more than one
      // step is too imprecise
      impreciseMatch(this, result)
      or
      exists(string lbl | result = getImpreciseMatchForPredecessor(lbl, this).getASuccessor(lbl))
    }

    string toString() { result = getPath() }
  }

  pragma[noinline]
  pragma[nomagic]
  private LocalApiGraph::Node getAPredecessorLocal(RemoteApiGraph::Node rem, string lbl) {
    match(rem.getAPredecessor(lbl), result)
  }

  private predicate match(RemoteApiGraph::Node rem, LocalApiGraph::Node loc) {
    rem = MkRootNode(_) and
    loc = LocalApiGraph::root()
    or
    exists(string lbl | loc = getAPredecessorLocal(rem, lbl).getASuccessor(lbl))
  }

  pragma[noinline]
  private LocalApiGraph::Node getAMemberPredecessorLocal(RemoteApiGraph::Node rem) {
    result = getAPredecessorLocal(rem, Label::member(_))
  }

  pragma[noinline]
  private predicate impreciseMatch(RemoteApiGraph::Node rem, LocalApiGraph::Node loc) {
    getAMemberPredecessorLocal(rem).getUnknownMember() = loc
  }

  pragma[noinline]
  private LocalApiGraph::Node getImpreciseMatchForPredecessor(string lbl, RemoteApiGraph::Node rem) {
    impreciseMatch(rem.getAPredecessor(lbl), result)
  }

  class RootNode extends Node, MkRootNode {
    override LocalApiGraph::RootNode getLocalNode() { result = Node.super.getLocalNode() }
  }

  class DefNode extends Node, MkDefNode {
    override LocalApiGraph::UseNode getLocalNode() { result = Node.super.getLocalNode() }
  }

  class UseNode extends Node, MkUseNode {
    override LocalApiGraph::DefNode getLocalNode() { result = Node.super.getLocalNode() }
  }
}
