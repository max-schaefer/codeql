/**
 * Provides classes importing source and sink summaries.
 *
 * Import this from `javascript.qll` to have all security queries make use of summaries
 * (if there are any).
 */

import javascript
import ApiGraphs
private import external.ExternalArtifact

private predicate matchLabel(DataFlow::FlowLabel lbl, string spec) {
  lbl.toString() = spec
  or
  lbl.isData() and
  spec = ""
}

private predicate matchConfig(DataFlow::Configuration cfg, string spec) {
  cfg.toString() = spec
  or
  spec = ""
}

private class RemoteSource extends DataFlow::AdditionalSource {
  string labelSpec;
  string configSpec;

  RemoteSource() {
    exists(ExternalData e, RemoteApiGraph::Node nd |
      e.getField(0) = "sourceSummary" and
      nd.getPath() = e.getField(1) and
      labelSpec = e.getField(2) and
      configSpec = e.getField(3) and
      this = nd.getLocalNode().getAUse()
    )
  }

  override predicate isSourceFor(DataFlow::Configuration cfg, DataFlow::FlowLabel lbl) {
    matchLabel(lbl, labelSpec) and
    matchConfig(cfg, configSpec)
  }
}

private class RemoteSink extends DataFlow::AdditionalSink {
  string labelSpec;
  string configSpec;

  RemoteSink() {
    exists(ExternalData e, RemoteApiGraph::Node nd |
      e.getField(0) = "sinkSummary" and
      nd.getPath() = e.getField(1) and
      labelSpec = e.getField(2) and
      configSpec = e.getField(3) and
      this = nd.getLocalNode().getADefinition()
    )
  }

  override predicate isSinkFor(DataFlow::Configuration cfg, DataFlow::FlowLabel lbl) {
    matchLabel(lbl, labelSpec) and
    matchConfig(cfg, configSpec)
  }
}

private class PropagationSummary extends DataFlow::AdditionalFlowStep {
  RemoteApiGraph::Node i;
  RemoteApiGraph::Node o;

  PropagationSummary() {
    exists(ExternalData e |
      e.getField(0) = "propagationSummary" and
      i.getPath() = e.getField(1) and
      o.getPath() = e.getField(2)
    ) and
    this = DataFlow::globalAccessPathRootPseudoNode()
  }

  override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
    pred = i.getLocalNode().getADefinition() and
    succ = o.getLocalNode().getAUse()
  }
}
