import javascript

/**
 * Holds if `rl` is a simple constant, which is bound to the result of the predicate.
 *
 * For example, `/a/g` has string value `"a"` and `/abc/` has string value `"abc"`,
 * while `/ab?/` and `/a(?=b)/` do not have a string value.
 *
 * Flags are ignored, so `/a/i` is still considered to have string value `"a"`,
 * even though it also matches `"A"`.
 *
 * Note the somewhat subtle use of monotonic aggregate semantics, which makes the
 * `strictconcat` fail if one of the children of the root is not a constant (legacy
 * semantics would simply skip such children).
 */
language[monotonicAggregates]
string getStringValue(RegExpLiteral rl) {
  exists(RegExpTerm root | root = rl.getRoot() |
    result = root.(RegExpConstant).getValue()
    or
    result = strictconcat(RegExpTerm ch, int i |
        ch = root.(RegExpSequence).getChild(i)
      |
        ch.(RegExpConstant).getValue() order by i
      )
  )
}

/**
 * Holds if `metachar` is a meta-character that is used to escape special characters
 * into a form described by regular expression `regex`.
 */
predicate escapingScheme(string metachar, string regex) {
  exists(string hexdigits | hexdigits = "[a-fA-F0-9]+" |
    metachar = "&" and regex = "&(\\w|#\\d+|#[xX]" + hexdigits + ");"
    or
    metachar = "%" and regex = "%" + hexdigits
    or
    metachar = "\\" and
    regex = "\\\\(.|\\d+|x" + hexdigits + "|u" + hexdigits + "|u\\{" + hexdigits + "\\})"
  )
}

/**
 * A method call that performs string replacement.
 */
abstract class Replacement extends DataFlow::Node {
  /**
   * Holds if this replacement replaces the string `input` with `output`.
   */
  abstract predicate replaces(string input, string output);

  /**
   * Gets the input of this replacement.
   */
  abstract DataFlow::Node getInput();

  /**
   * Gets the output of this replacement.
   */
  abstract DataFlow::SourceNode getOutput();

  /**
   * Holds if this replacement escapes `char` using `metachar`.
   *
   * For example, during HTML entity escaping `<` is escaped (to `&lt;`)
   * using `&`.
   */
  predicate escapes(string char, string metachar) {
    exists(string regexp, string repl |
      escapingScheme(metachar, regexp) and
      replaces(char, repl) and
      repl.regexpMatch(regexp)
    )
  }

  /**
   * Holds if this replacement unescapes `char` using `metachar`.
   *
   * For example, during HTML entity unescaping `<` is unescaped (from
   * `&lt;`) using `&`.
   */
  predicate unescapes(string metachar, string char) {
    exists(string regexp, string orig |
      escapingScheme(metachar, regexp) and
      replaces(orig, char) and
      orig.regexpMatch(regexp)
    )
  }
}

/**
 * A call to `String.prototype.replace` that replaces all instances of a pattern.
 */
class GlobalStringReplacement extends Replacement, DataFlow::MethodCallNode {
  RegExpLiteral pattern;

  GlobalStringReplacement() {
    this.getMethodName() = "replace" and
    pattern.flow().(DataFlow::SourceNode).flowsTo(this.getArgument(0)) and
    this.getNumArgument() = 2 and
    pattern.isGlobal()
  }

  override predicate replaces(string input, string output) {
    input = getStringValue(pattern) and
    output = this.getArgument(1).getStringValue()
    or
    exists(DataFlow::FunctionNode replacer, DataFlow::PropRead pr, DataFlow::ObjectLiteralNode map |
      replacer = getCallback(1) and
      replacer.getParameter(0).flowsToExpr(pr.getPropertyNameExpr()) and
      pr = map.getAPropertyRead() and
      pr.flowsTo(replacer.getAReturn()) and
      map.asExpr().(ObjectExpr).getPropertyByName(input).getInit().getStringValue() = output
    )
  }

  override DataFlow::Node getInput() { result = this.getReceiver() }

  override DataFlow::SourceNode getOutput() { result = this }
}

/**
 * A call to `JSON.stringify`, viewed as a string replacement.
 */
class JsonStringifyReplacement extends Replacement, DataFlow::CallNode {
  JsonStringifyReplacement() { this = DataFlow::globalVarRef("JSON").getAMemberCall("stringify") }

  override predicate replaces(string input, string output) {
    input = "\\" and output = "\\\\"
    // the other replacements are not relevant for this query
  }

  override DataFlow::Node getInput() { result = this.getArgument(0) }

  override DataFlow::SourceNode getOutput() { result = this }
}

/**
 * A call to `JSON.parse`, viewed as a string replacement.
 */
class JsonParseReplacement extends Replacement {
  JsonParserCall self;

  JsonParseReplacement() { this = self }

  override predicate replaces(string input, string output) {
    input = "\\\\" and output = "\\"
    // the other replacements are not relevant for this query
  }

  override DataFlow::Node getInput() { result = self.getInput() }

  override DataFlow::SourceNode getOutput() { result = self.getOutput() }
}

/**
 * Gets the URI-encoded equivalent of `s`.
 *
 * This predicate only handles a few of the most important meta-characters.
 */
string uriEncode(string s) {
  s = "\"" and result = "%22"
  or
  s = "%" and result = "%25"
  or
  s = "&" and result = "%26"
  or
  s = "<" and result = "%3C"
  or
  s = ">" and result = "%3E"
  or
  s = "\\" and result = "%5C"
}

/**
 * A call to `encodeURI` or `encodeURIComponent`, viewed as a string replacement.
 */
class UriEncoding extends Replacement, DataFlow::CallNode {
  UriEncoding() {
    this = DataFlow::globalVarRef("encodeURI").getACall() or
    this = DataFlow::globalVarRef("encodeURIComponent").getACall() or
    this = DataFlow::moduleMember("url", "pathToFileURL").getACall() or
    this = DataFlow::moduleMember("urijs", "encode").getACall() or
    this = DataFlow::moduleMember("urijs", "encodeQuery").getACall() or
    this = DataFlow::moduleMember("urijs", "encodeReserved").getACall() or
    this = DataFlow::moduleMember("urijs", "encodePathSegment").getACall() or
    this = DataFlow::moduleMember("urijs", "encodeUrnPathSegment").getACall() or
    this = DataFlow::moduleMember("uri-js", "pctEncChar").getACall() or
    this = DataFlow::moduleMember("uri-js", "escapeComponent").getACall() or
    this = DataFlow::moduleMember("query-string", "stringify").getACall() or
    this = DataFlow::moduleMember("querystring", "encode").getACall() or
    this = DataFlow::moduleMember("querystring", "escape").getACall() or
    this = DataFlow::moduleMember("querystring", "parse").getACall() or
    this = DataFlow::moduleMember("querystring", "stringify").getACall() or
    this = DataFlow::moduleMember("querystringify", "stringify").getACall() or
    this = DataFlow::moduleImport("strict-uri-encode").getACall()
  }

  override predicate replaces(string input, string output) { output = uriEncode(input) }

  override DataFlow::Node getInput() { result = this.getArgument(0) }

  override DataFlow::SourceNode getOutput() { result = this }
}

/**
 * A call to `decodeURI` or `decodeURIComponent`, viewed as a string replacement.
 */
class UriDecoding extends Replacement, DataFlow::CallNode {
  UriDecoding() {
    this = DataFlow::globalVarRef("decodeURI").getACall() or
    this = DataFlow::globalVarRef("decodeURIComponent").getACall() or
    this = DataFlow::moduleMember("url", "domainToASCII").getACall() or
    this = DataFlow::moduleMember("url", "domainToUnicode").getACall() or
    this = DataFlow::moduleMember("url", "fileURLToPath").getACall() or
    this = DataFlow::moduleMember("urijs", "decode").getACall() or
    this = DataFlow::moduleMember("urijs", "decodeQuery").getACall() or
    this = DataFlow::moduleMember("urijs", "decodePath").getACall() or
    this = DataFlow::moduleMember("urijs", "decodePathSegment").getACall() or
    this = DataFlow::moduleMember("urijs", "decodeUrnPath").getACall() or
    this = DataFlow::moduleMember("urijs", "decodeUrnPathSegment").getACall() or
    this = DataFlow::moduleMember("urijs", "parseQuery").getACall() or
    this = DataFlow::moduleMember("uri-js", "normalize").getACall() or
    this = DataFlow::moduleMember("uri-js", "pctDecChars").getACall() or
    this = DataFlow::moduleMember("uri-js", "unescapeComponent").getACall() or
    this = DataFlow::moduleMember("query-string", "parse").getACall() or
    this = DataFlow::moduleMember("query-string", "parseUrl").getACall() or
    this = DataFlow::moduleMember("querystring", "unescapeBuffer").getACall() or
    this = DataFlow::moduleMember("querystring", "unescape").getACall() or
    this = DataFlow::moduleMember("querystring", "parse").getACall() or
    this = DataFlow::moduleMember("querystring", "decode").getACall() or
    this = DataFlow::moduleMember("querystringify", "parse").getACall()
  }

  override predicate replaces(string input, string output) { input = uriEncode(output) }

  override DataFlow::Node getInput() { result = this.getArgument(0) }

  override DataFlow::SourceNode getOutput() { result = this }
}
