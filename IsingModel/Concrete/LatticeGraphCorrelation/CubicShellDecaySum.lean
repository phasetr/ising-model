import IsingModel.Concrete.LatticeGraphCorrelation.CubicShellDecaySum.ShellDecaySumBound
import IsingModel.Concrete.LatticeGraphCorrelation.CubicShellDecaySum.CorrelationIncrementPolyPow
import IsingModel.Concrete.LatticeGraphCorrelation.CubicShellDecaySum.SeparationHypothesis
import IsingModel.Concrete.LatticeGraphCorrelation.CubicShellDecaySum.GeometricUniformBounds

/-!
# Cubic-shell tight `derivBoundTight` bounded by a spatial-decay sum (Issue #2965, Phase B)

Applies the infinite-volume spatial exponential decay
`correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair` termwise to
the diagonal-free cubic-shell bound
`derivBoundTight_inducedGraph_cubic_le_infiniteVolume_sum`, replacing each
infinite-volume two-point correlation `g{x,y}` by its decay bound
`(contractionFactor)^{dist(x,y)/(r₀+2)}`.

Because the tight bound carries only the cross products
`g{r,a}·g{s,b} + g{r,b}·g{s,a}` (no diagonal `g{r,s}·g{a,b}` term), every factor
genuinely decays in the distance from `r`/`s` to the cut vertices, so this is the
diagonal-free decay-sum input from which a geometric per-stage rate is extracted
(the remaining shell-edge distance/counting aggregation is downstream).

## Main declaration

* `IsingModel.Ambient.derivBoundTight_inducedGraph_cubic_le_decay_sum`.

## Contents

The declarations live in four child modules, re-exported by this declaration-free facade:

* `Concrete.LatticeGraphCorrelation.CubicShellDecaySum.ShellDecaySumBound` — the geometric
  core: the termwise decay-sum bound on the diagonal-free cubic-shell tight bound, the
  geometric decay of a `contractionFactor` power at a fresh cubic vertex, the fresh-vertex
  property of a straddle edge, the per-stage shell bound in
  `card • (2 · cf^{(k+1−R)/(r₀+2)})` form, the cubic shell edge-count bound `d·(2(k+1)+1)^d`,
  and the resulting polynomial × geometric shell bound.
* `Concrete.LatticeGraphCorrelation.CubicShellDecaySum.CorrelationIncrementPolyPow` — the
  transport of the shell bound to the per-stage correlation increment along the cubic
  exhaustion: the one-sided polynomial × geometric increment, its two-sided absolute form
  from ferromagnetic monotonicity, the direct `correlation` form on the induced cubic
  graphs, and the high-temperature simplification to `(2k+3)^d · cf^{(k+1−R)/(r₀+2)}`.
* `Concrete.LatticeGraphCorrelation.CubicShellDecaySum.SeparationHypothesis` — the
  combinatorics auto-discharging the separation hypothesis `hsep`: a `latticeGraph`
  neighbour of a site of `box_R` lies in `box_{R+1}`, hence for `R + 1 ≤ k` a lifted site of
  `box_R` is an endpoint of no straddle edge of stage `k+1`, together with the pair version.
* `Concrete.LatticeGraphCorrelation.CubicShellDecaySum.GeometricUniformBounds` — the
  analytic floor-power → geometric conversion `cf^⌊n/m⌋ ≤ (1/cf) · (cf^{1/m})^n` and the
  compositions it enables: the clean geometric high-temperature form of the cubic absolute
  increment, the `cf_max` uniformization removing the β-dependence, and the fully uniform
  geometric high-temperature bound.
-/
