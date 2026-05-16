import IsingModel.Concrete.LatticeGraphBED
import IsingModel.ComplexAnalyticity
import IsingModel.AmbientComplexAnalyticity
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexAnalyticityBasic
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexAnalyticityBasicPartitionSingle
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexRealCompat
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexRealCompatLeeYangSubdomain
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexContinuityNorm
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexContinuityNormContinuous
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexBranches
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexBranchesLogZ
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexSlitPlane
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexRestrictions
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexRestrictionsRealParams
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexBranchEntire
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexBranchEntireContinuity
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexIsingPoly

/-!
# ℤ^d real/complex analyticity wrappers (fixed-Λ)

Direct ℤ^d forwarders for:

* Real analyticity of `partitionFunctionΛ` / `freeEnergyH` / `freeEnergyJ`
  (using `IsingModel/FreeEnergy.lean`).
* Complex analyticity of `partitionFunctionComplex` / `freeEnergyComplex`
  (GJ §4.6 Thm 4.6.2; using `IsingModel/ComplexAnalyticity.lean` and
  `IsingModel/AmbientComplexAnalyticity.lean`).
* Lee–Yang non-vanishing: `partitionFunctionComplex_nonzero_of_leeYang_*`.
* Slit-plane membership and `freeEnergyComplex` log-branch wrappers.
* `isingEdgePoly` / `leeYangFugacityVec` product expansion.

All theorems are thin pass-throughs of the abstract results in
`ComplexAnalyticity.lean` / `AmbientComplexAnalyticity.lean` applied to the
concrete `Ambient.inducedGraph (IsingModel.latticeGraph d) Λ` at a fixed
finite `Λ : Finset (Fin d → ℤ)`.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.6, pp. 68–70.
-/

namespace IsingModel

namespace Ambient

/-! ## Moved: per-direction analyticity wrappers (real and complex)

The 12 concrete per-direction `analyticAt` / `analyticOn` wrappers
for `partitionFunction*` / `freeEnergy*` in `h`, `J`, `β` (plus joint
analyticity) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.ComplexAnalyticityBasic`.
The earlier import path is preserved by re-importing the new child.
-/



/-! ## Moved: real-complex compatibility / Lee-Yang domain wrappers

The 22 concrete real-complex compatibility, Lee-Yang-domain
non-vanishing, and related restriction wrappers on `latticeGraph d`
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.ComplexRealCompat`.
The earlier import path is preserved by re-importing the new child.
-/


/-! #### Continuity, analyticOn, and norm bounds for complex Z / f

Direct ℤ^d forwarders for continuity, universe / Lee-Yang-domain
`AnalyticOn` restatements, and locally-uniform norm bounds on
`partitionFunctionComplex` / `freeEnergyComplex`. These are the
Montel + Vitali inputs for the infinite-volume completion at ℤ^d. -/


/-! ## Moved: continuity / analyticOn / norm-bound wrappers

The 15 concrete continuity, `AnalyticOnNhd`/`AnalyticOn`, and
norm-bound wrappers for `partitionFunctionComplex` / `freeEnergyComplex`
on `latticeGraph d` now live in
`IsingModel.Concrete.LatticeGraphCorrelation.ComplexContinuityNorm`.
The earlier import path is preserved by re-importing the new child.
-/


/-! #### Local `log Z` / `freeEnergyComplex` branch on Lee-Yang domain

Direct ℤ^d forwarders for the `exists_logZ_*` / `exists_freeEnergyComplex_*`
local-branch construction, the `partitionFunctionComplex` non-vanishing
on `leeYangSubdomain` / `leeYangDomain`, and the principal-branch
`freeEnergyComplex` `AnalyticOnNhd` on its analyticity locus. These are
the finite-volume GJ §4.6 Thm 4.6.2 branch-form ingredients at ℤ^d. -/

/-! ## Moved: log-branch construction wrappers

The 11 concrete log Z / freeEnergyComplex local-branch construction
wrappers on `latticeGraph d` now live in
`IsingModel.Concrete.LatticeGraphCorrelation.ComplexBranches`.
The earlier import path is preserved by re-importing the new child.
-/


/-! #### slitPlane-locus analyticity + log-branch basepoint evaluation

Direct ℤ^d forwarders for the remaining continuity / differentiable /
analytic-on-slitPlane-locus theorems (h-variable and joint (J, h, β)),
the log-branch basepoint identities, and auxiliary `exists_logZ_*`
ball restatements from `IsingModel/ComplexAnalyticity.lean`. -/

/-! ## Moved: slitPlane-locus + log-branch-on-ball wrappers

The 15 concrete slitPlane-locus continuity / analyticOn / differentiableOn
wrappers and log-branch-on-ball wrappers on `latticeGraph d` now live in
`IsingModel.Concrete.LatticeGraphCorrelation.ComplexSlitPlane`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: leeYang inclusions + real-axis restriction wrappers

The 16 concrete leeYangSubdomain ⊆ slitPlane locus inclusions and
real-axis restriction identities now live in
`IsingModel.Concrete.LatticeGraphCorrelation.ComplexRestrictions`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: analyticBranch + entire wrappers

The 12 concrete `leeYangDomain_subset_branch_locus`,
`freeEnergyComplex_exists_analyticBranch*`,
`analyticBranch_freeEnergyComplex_*`,
`continuous_freeEnergyComplex_on_locus`,
`continuousAt/differentiableAt_freeEnergyComplex_at_real_joint`, and
`partitionFunctionComplex_entire_*` wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.ComplexBranchEntire`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: isingEdgePoly + Hamiltonian + miscellaneous wrappers

The final 10 concrete `isingEdgePoly` evaluations,
`exp_neg_beta_hamiltonian_*`, `prod_exp_beta_J_edgeSpin_eq`,
`exists_normalised_logZ_branch_on_ball`,
`partitionFunctionComplex_ne_zero_not_iff_slitPlane`, and
`norm_partitionFunctionComplex_eq_partitionFunction_at_real` wrappers
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.ComplexIsingPoly`.
The earlier import path is preserved by re-importing the new child.
-/

end Ambient
end IsingModel
