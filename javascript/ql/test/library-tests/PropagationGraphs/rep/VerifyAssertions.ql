import javascript
import NodeRepresentation

class Assertion extends Comment {
  boolean asRhs;
  string ap;

  Assertion() {
    asRhs = true and
    ap = getText().regexpCapture("\\s*candidateRep: rhs (\\(.*\\))\\s*", 1)
    or
    asRhs = false and
    ap = getText().regexpCapture("\\s*candidateRep: (\\(.*\\))\\s*", 1)
  }

  predicate holds() {
    exists(DataFlow::Node nd, string file, int startLine |
      getLocation().hasLocationInfo(file, startLine, _, _, _) and
      nd.hasLocationInfo(file, startLine, _, _, _) and
      ap = candidateRep(nd, _, asRhs)
    )
  }

  override string toString() {
    exists(string file, int startLine |
      getLocation().hasLocationInfo(file, startLine, _, _, _) and
      result =
        "candidateRep(nd, _, " + asRhs + ") = \"" + ap + "\" for some node nd on line " + startLine +
          " of file " + file
    )
  }
}

from Assertion a
where not a.holds()
select a, "Assertion does not hold."
