import PropagationGraphs

class AllPackagesAreInteresting extends InterestingPackage {
  AllPackagesAreInteresting() { exists(API::moduleImport(this)) }
}

from DataFlow::Node src, DataFlow::Node san, DataFlow::Node snk
where triple(src, san, snk)
select rep(src, false), rep(san, false), rep(snk, true)
