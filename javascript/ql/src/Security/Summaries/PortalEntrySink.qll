import javascript
import semmle.javascript.dataflow.Portals

/**
 * An escaping entry node of a portal, viewed as an additional sink node for any flow
 * configuration currently in scope.
 */
class PortalEntrySink extends DataFlow::AdditionalSink {
  EntryNode e;

  PortalEntrySink() { this = e.asDataFlowNode() }

  override predicate isSinkFor(DataFlow::Configuration cfg, DataFlow::FlowLabel lbl) { any() }

  /** Gets the portal node to which this corresponds. */
  EntryNode getPortalNode() { result = e }
}
