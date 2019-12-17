/**
 * Provides default sources, sinks and sanitizers for reasoning about
 * NoSQL injection vulnerabilities, as well as extension points for
 * adding your own.
 */

import javascript
import semmle.javascript.security.TaintedObject

module NosqlInjection {
  /**
   * A data flow source for NoSQL injection vulnerabilities.
   */
  abstract class Source extends DataFlow::Node {
    /**
     * Gets a flow label relevant for this source.
     */
    DataFlow::FlowLabel getAFlowLabel() { result = DataFlow::FlowLabel::data() }
  }

  /**
   * A data flow sink for NoSQL injection vulnerabilities.
   */
  abstract class Sink extends DataFlow::Node {
    /**
     * Gets a flow label relevant for this sink.
     *
     * Defaults to deeply tainted objects only.
     */
    DataFlow::FlowLabel getAFlowLabel() { result = TaintedObject::label() }
  }

  /**
   * A sanitizer for NoSQL injection vulnerabilities.
   */
  abstract class Sanitizer extends DataFlow::Node { }

  /**
   * An additional flow step to consider when checking for NoSQL injection vulnerabilities.
   */
  abstract class AdditionalFlowStep extends string {
    bindingset[this]
    AdditionalFlowStep() { any() }

    abstract predicate step(
      DataFlow::Node src, DataFlow::Node trg, DataFlow::FlowLabel inlbl, DataFlow::FlowLabel outlbl
    );
  }

  /** A source of remote user input, considered as a flow source for NoSQL injection. */
  class RemoteFlowSourceAsSource extends Source {
    RemoteFlowSourceAsSource() { this instanceof RemoteFlowSource }
  }

  /** A source of tainted objects, considered as a flow source for NoSQL injection. */
  class TaintedObjectSource extends Source {
    TaintedObjectSource() { TaintedObject::isSource(this, _) }

    override DataFlow::FlowLabel getAFlowLabel() { TaintedObject::isSource(this, result) }
  }

  /** An expression interpreted as a NoSQL query, viewed as a sink. */
  class NosqlQuerySink extends Sink, DataFlow::ValueNode {
    override NoSQL::Query astNode;
  }

  /** A step through tainted objects, used to check for NoSQL injection vulnerabilities. */
  class TaintedObjectStep extends AdditionalFlowStep {
    TaintedObjectStep() { this = "TaintedObjectStep" }

    override predicate step(
      DataFlow::Node src, DataFlow::Node trg, DataFlow::FlowLabel inlbl, DataFlow::FlowLabel outlbl
    ) {
      TaintedObject::step(src, trg, inlbl, outlbl)
    }
  }

  /** A step through NoSQL query objects, used to check for NoSQL injection vulnerabilities. */
  class NosqlQueryObjectStep extends AdditionalFlowStep {
    NosqlQueryObjectStep() { this = "NosqlQueryObjectStep" }

    override predicate step(
      DataFlow::Node src, DataFlow::Node trg, DataFlow::FlowLabel inlbl, DataFlow::FlowLabel outlbl
    ) {
      inlbl = TaintedObject::label() and
      outlbl = TaintedObject::label() and
      exists(NoSQL::Query query, DataFlow::SourceNode queryObj |
        queryObj.flowsToExpr(query) and
        queryObj.flowsTo(trg) and
        src = queryObj.getAPropertyWrite().getRhs()
      )
    }
  }
}
