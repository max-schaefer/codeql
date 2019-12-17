/**
 * Provides a taint tracking configuration for reasoning about NoSQL
 * injection vulnerabilities.
 *
 * Note, for performance reasons: only import this file if
 * `NosqlInjection::Configuration` is needed, otherwise
 * `NosqlInjectionCustomizations` should be imported instead.
 */

import javascript
import semmle.javascript.security.TaintedObject

module NosqlInjection {
  import NosqlInjectionCustomizations::NosqlInjection

  /**
   * A taint-tracking configuration for reasoning about SQL-injection vulnerabilities.
   */
  class Configuration extends TaintTracking::Configuration {
    Configuration() { this = "NosqlInjection" }

    override predicate isSource(DataFlow::Node source, DataFlow::FlowLabel label) {
      source.(Source).getAFlowLabel() = label
    }

    override predicate isSink(DataFlow::Node sink, DataFlow::FlowLabel label) {
      sink.(Sink).getAFlowLabel() = label
    }

    override predicate isSanitizer(DataFlow::Node node) {
      super.isSanitizer(node) or
      node instanceof Sanitizer
    }

    override predicate isSanitizerGuard(TaintTracking::SanitizerGuardNode guard) {
      guard instanceof TaintedObject::SanitizerGuard
    }

    override predicate isAdditionalFlowStep(
      DataFlow::Node src, DataFlow::Node trg, DataFlow::FlowLabel inlbl, DataFlow::FlowLabel outlbl
    ) {
      any(AdditionalFlowStep afs).step(src, trg, inlbl, outlbl)
    }
  }
}
