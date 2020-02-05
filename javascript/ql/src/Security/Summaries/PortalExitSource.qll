import javascript
import semmle.javascript.dataflow.Portals

/**
 * A remote exit node of a portal, viewed as an additional source node for any flow
 * configuration currently in scope.
 */
class PortalExitSource extends DataFlow::AdditionalSource {
  ExitNode x;

  PortalExitSource() { this = x.asDataFlowNode() }

  override predicate isSourceFor(DataFlow::Configuration cfg, DataFlow::FlowLabel lbl) { any() }

  /** Gets the portal node to which this corresponds. */
  ExitNode getPortalNode() { result = x }
}
