import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.EventualClosedBallPatches.ClosedBallLocal.RelCompactPatch
import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.EventualClosedBallPatches.ClosedBallLocal.DirectRangePatch
import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.EventualClosedBallPatches.ClosedBallLocal.ViaDeviationDirectRange
import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.EventualClosedBallPatches.ClosedBallLocal.EventualOverlapClosedBall
import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.EventualClosedBallPatches.ClosedBallLocal.EventualOverlapDeviation

/-!
# Per-stage complex analyticity wrappers: ClosedBallLocal

Consolidated `ClosedBallLocal` wrappers for the GJ §17.5.2 / §4.6
Vitali–Montel route (per-stage complex partition-function
analyticity).  Merged from the former one-declaration-per-file
fragments; declarations and proofs are unchanged.

## Contents

The declarations live in five child modules, re-exported by this declaration-free facade:

* `….ClosedBallLocal.RelCompactPatch` — the non-range closed-ball relative-compactness
  route: closed-ball branch-local Ascoli data feeding the branch locally bounded
  relative-compactness patch and its compact-target form, the `direct` variant that forgets
  the closed-ball containment together with its compact-target and positive-real endpoints,
  and the positive-real compact-target endpoint of the plain patch route.
* `….ClosedBallLocal.DirectRangePatch` — the direct closed-ball branch-local *range* route:
  closed-ball branch locally bounded data converted directly to relatively compact range
  data before the all-stage range patch endpoint, its compact-target form, and the
  positive-real compact-target endpoint of the same route.
* `….ClosedBallLocal.ViaDeviationDirectRange` — the via-deviation direct-range route, in
  which closed-ball branch-local boundedness is converted through closed-ball
  branch-deviation data using the automatic closed-ball principal free-energy bound before
  direct-range patching: the abstract patch, its compact-target form and the positive-real
  compact-target endpoint.
* `….ClosedBallLocal.EventualOverlapClosedBall` — the eventual-overlap closed-ball
  branch-local direct-range route, where coherent selected-overlap equality is supplied by
  the pointwise-normalised eventual-overlap package: the abstract patch and its
  compact-target form.
* `….ClosedBallLocal.EventualOverlapDeviation` — the eventual-overlap branch-deviation
  direct-range route: deviation Ascoli data feeding the direct relatively compact range
  route, and the via-local variant in which deviation bounds together with the explicit
  principal free-energy bound supply branch-local boundedness; each in an abstract and a
  compact-target form.
-/
