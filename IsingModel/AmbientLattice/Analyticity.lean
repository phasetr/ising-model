import IsingModel.AmbientLattice.Defs
import IsingModel.ClusterExpansion
import IsingModel.AmbientLattice.AnalyticityLambdaJoint
import IsingModel.AmbientLattice.AnalyticityLambdaMagSuscep
import IsingModel.AmbientLattice.AnalyticityLambdaPerDirection
import IsingModel.AmbientLattice.AnalyticityLambdaPolymer
import IsingModel.AmbientLattice.AnalyticityLambdaSandwich
import IsingModel.AmbientLattice.AnalyticityLambdaRegularity
import IsingModel.AmbientLattice.AnalyticityLambdaPolymerBounds
import IsingModel.AmbientLattice.AnalyticityLambdaMayer
import IsingModel.AmbientLattice.AnalyticityLambdaVdPolymer
import IsingModel.AmbientLattice.AnalyticityLambdaMayerIdentity
import IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds
import IsingModel.AmbientLattice.AnalyticityLambdaMayerRecurrenceEpsilon
import IsingModel.AmbientLattice.AnalyticityLambdaEpsilonIff
import IsingModel.AmbientLattice.AnalyticityLambdaTanhFerroIff
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening
import IsingModel.AmbientLattice.AnalyticityLambdaSection186
import IsingModel.AmbientLattice.AnalyticityLambdaCapstones

/-!
# Joint analyticity for AmbientLattice finite-volume Λ-restricted Ising

Lifts the joint analyticity of `partitionFunction` and `freeEnergy` in
`(β, J, h) ∈ ℝ × ℝ × ℝ` (Glimm-Jaffe §18.6 capstone, established in
`IsingModel/ClusterExpansion.lean` via direct sum-of-exp analyticity)
to the finite-volume Λ-restricted versions defined in
`IsingModel/AmbientLattice/Defs.lean`. Each theorem is a thin wrapper
around the corresponding theorem on `inducedGraph G Λ`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-! ## Moved: Λ-level joint analyticity wrappers

The 10 Λ-level joint analyticity wrappers (partitionFunctionΛ +
freeEnergyΛ + correlationΛ AnalyticAt / AnalyticOnNhd / Continuous /
Differentiable joint) now live in
`IsingModel.AmbientLattice.AnalyticityLambdaJoint`.
The earlier import path is preserved by re-importing the new child.
-/



/-! ## Moved: magnetizationΛ + susceptibilityΛ analyticity wrappers

The 14 magnetizationΛ + susceptibilityΛ + correlationΛ
continuousAt/differentiableAt/analyticAt/analyticOnNhd joint wrappers
now live in
`IsingModel.AmbientLattice.AnalyticityLambdaMagSuscep`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: Λ partitionFunction per-direction regularity wrappers

The 6 partitionFunctionΛ per-direction Continuous / Differentiable
wrappers at general h now live in
`IsingModel.AmbientLattice.AnalyticityLambdaPerDirection`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## §18.4-§18.5 polymerFreeEnergy / vdSum / ε wrappers (now split)

The Λ-layer wrappers for the §18.4-§18.5 polymerFreeEnergy /
vdPolymerFamilies_sum / mayerPartialSum / mayerExpansionTerm /
ε(t) / log_vdPolymerFamilies_sum / Mayer identity / strict-mono /
iff family bundles originally lived inline below this header. They
have been refactored out into narrow child modules
(`AnalyticityLambdaPolymer`, `AnalyticityLambdaSandwich`,
`AnalyticityLambdaPolymerBounds`, `AnalyticityLambdaMayer`,
`AnalyticityLambdaVdPolymer`, `AnalyticityLambdaMayerIdentity`,
`AnalyticityLambdaBasicIdentities`,
`AnalyticityLambdaMayerPfeEdgeBounds`,
`AnalyticityLambdaMayerRecurrenceEpsilon`,
`AnalyticityLambdaEpsilonIff`, ...) re-imported at the top of this
file, so the earlier import path is preserved while the per-PR
narrow Moved doc blocks below list the exact destinations. -/

/-! ## Moved: polymerFreeEnergy_Λ basic wrappers

The 16 §18.4 polymerFreeEnergy_Λ / vdPolymerFamilies_sum_Λ / mayer*_Λ
basic wrappers now live in
`IsingModel.AmbientLattice.AnalyticityLambdaPolymer`.
The earlier import path is preserved by re-importing the new child.
-/



/-! ## Moved: polymerFreeEnergy_Λ sandwich + hasSum wrappers

The 10 §18.4 / §18.5 polymerFreeEnergy_Λ high_temp_sandwich, tanh
sandwich, hasSum_via_log, and vdPolymerFamilies_sum_Λ sandwich wrappers
(with ferromagnetic variants) now live in
`IsingModel.AmbientLattice.AnalyticityLambdaSandwich`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: Λ regularity wrappers

The 10 Λ-layer freeEnergyΛ correction + polymerFreeEnergy_Λ
continuous/differentiable + tanh analyticAt/analyticOnNhd wrappers
now live in
`IsingModel.AmbientLattice.AnalyticityLambdaRegularity`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: polymerFreeEnergy_Λ bounds wrappers

The 12 Λ-layer polymerFreeEnergy_Λ nonneg / bounds / monotone / eq_zero
/ tanh sandwich / tanh double bound wrappers now live in
`IsingModel.AmbientLattice.AnalyticityLambdaPolymerBounds`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: mayer wrappers

The 23 §18.6 mayerPartialSum_Λ + mayerExpansionTerm_Λ
continuous/differentiable/analyticAt/analyticOnNhd wrappers (raw and
tanh-composed variants) now live in
`IsingModel.AmbientLattice.AnalyticityLambdaMayer`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: vdPolymerFamilies_sum + log_vdPolymerFamilies_sum wrappers

The 14 §18.5-18.6 vdPolymerFamilies_sum_Λ + log_vdPolymerFamilies_sum_Λ
continuous / differentiable / analyticAt / hasDerivAt wrappers
(raw and tanh-composed variants) now live in
`IsingModel.AmbientLattice.AnalyticityLambdaVdPolymer`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: §18.5 Mayer identity edge-case wrappers

The 19 §18.5 Λ-layer Mayer identity / polymerFreeEnergy =
mayerPartialSum edge-case wrappers (parameter slices `t = 0`, `β·J =
0`, `β = 0`, `J = 0`; polymer_free_energy form; mayerPartialSum 0 ≤
polymerFreeEnergy bounds; no-polymer / trivial / edgeless induced
graphs) now live in
`IsingModel.AmbientLattice.AnalyticityLambdaMayerIdentity`. The
earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: §18.5 basic identities + bounds + iff wrappers

The 17 §18.5 Λ-layer wrappers covering `at_zero` / `at_one` basic
identities, tanh iff characterizations, the bound family
(`le_two_pow`, `le_one_plus_tanh_pow`, `one_le_vdPolymerFamilies_sum_Λ`),
and generic-`t` bounds + `_eq_one_add` decomposition now live in
`IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities`. The
earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: §18.5 Mayer expansion + polymerFreeEnergy bound wrappers

The 17 §18.5 Λ-layer wrappers covering Mayer expansion edge-cases
(`n = 2`, `_two_filter`, `mayerPartialSum at N = 2`,
`_eq_zero_of_no_polymers`, `_eq_zero_of_edgeFinset_empty`,
`mayerExpansionTerm_abs_le`), polymerFreeEnergy at_zero / at_one +
analyticAt + analyticOnNhd_Ici_zero + sandwich_of_nonneg, and
polymerFreeEnergy tanh-bound + ferromagnetic + hasDerivAt +
`_eq_log_one_add_eps` now live in
`IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds`. The
earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: §18.5 Mayer recurrence + ε infrastructure wrappers

The 12 §18.5 Λ-layer wrappers covering Mayer recurrence
(`mayerPartialSum_Λ_succ`,
`mayerExpansionTerm_Λ_eq_mayerPartialSum_diff`),
`polymerFreeEnergy_Λ_hasSum_via_log` / `_hasSum_via_log_eventually`,
`vdPolymerFamilies_sum_Λ_minus_one_tendsto_zero`, Mayer term sign at
`n = 1, 2` (`mayerExpansionTerm_Λ_one_nonneg_of_nonneg`,
`_two_nonpos_of_nonneg`), `vdPolymerFamilies_sum_Λ_minus_one_{at_zero,
continuous, analyticAt, lt_one_eventually}`, and
`allPolymers_Λ_eq_empty_of_edgeFinset_empty` now live in
`IsingModel.AmbientLattice.AnalyticityLambdaMayerRecurrenceEpsilon`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: §18.5 ε(t) positivity-iff + strict-mono wrappers

The 16 §18.5 Λ-layer wrappers covering ε(t) / polymerFreeEnergy
positivity / zero iff family (`_minus_one_{pos_iff, eq_zero_iff,
tanh_pos_iff, tanh_eq_zero_iff}`, `polymerFreeEnergy_Λ_tanh_{pos_iff,
eq_zero_iff}`) and strict-mono / strict-pos under polymers ≠ ∅
(`_lt_of_lt`, `_strictMonoOn`, `_pos_of_t_pos`, `_gt_one_of_t_pos`,
`_minus_one_pos_of_t_pos`, `_tanh_pos_of_tanh_pos`,
`_tanh_gt_one_of_tanh_pos`, `_minus_one_tanh_pos_of_tanh_pos`,
`_strictMonoOn_Ioi_zero`, both for `polymerFreeEnergy_Λ` and
`vdPolymerFamilies_sum_Λ`) now live in
`IsingModel.AmbientLattice.AnalyticityLambdaEpsilonIff`. The earlier
import path is preserved by re-importing the new child.
-/


/-! ## Moved: §18.5 tanh ferromagnetic iff wrappers

The 9 §18.5 Λ-layer wrappers covering
`polymerFreeEnergy_Λ_tanh_{lt_eps_iff_eps_pos,
eq_zero_iff_eps_eq_zero, pos_iff_eps_pos, pos_iff, eq_zero_iff,
lt_pow_sub_one_of_eps_pos, lt_eps_of_eps_pos}_ferro` and
`vdPolymerFamilies_sum_Λ_tanh_{gt_one_iff, eq_one_iff}_ferro`
(under `0 ≤ β`, `0 ≤ J`) now live in
`IsingModel.AmbientLattice.AnalyticityLambdaTanhFerroIff`. The
earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: §18.5 polymerFreeEnergy sharpening + vdSum sandwich wrappers

The 21 §18.5 Λ-layer wrappers covering polymerFreeEnergy tanh
sharpening (non-ferromagnetic) + β/J strict-mono, ε(t) nonneg +
non-tanh polymerFreeEnergy sharpening, and vdSum sandwich/monotone
+ ε bound + pFE(tanh) bound + `log 2` (covering Λ-direct
`polymerFreeEnergy_Λ_tanh_*` sharpening, β/J strict-mono under
`polymers_nonempty`, `vdPolymerFamilies_sum_Λ_minus_one` nonneg
and pow_at_zero, non-tanh `polymerFreeEnergy_Λ` sharpening,
`vdPolymerFamilies_sum_Λ` sandwich/monotone/`minus_one_le`, and
`polymerFreeEnergy_Λ_tanh_{le_eps, le_pow_sub_one, lt_log_two}`)
now live in
`IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening`. The
earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: §18.6 partitionFunction + freeEnergy regularity wrappers

The 23 §18.6 Λ-layer wrappers covering partitionFunctionΛ regularity
at `h = 0`, freeEnergyΛ per-direction analyticity, and
partitionFunction joint + general-h analyticity now live in
`IsingModel.AmbientLattice.AnalyticityLambdaSection186`. The earlier
import path is preserved by re-importing the new child.
-/


/-! ## Moved: §18.4-§18.6 capstones + Mayer filter-connected wrappers

The 11 Λ-layer wrappers covering §18.4-§18.6 capstones
(partitionFunctionΛ high_temp_expansion, freeEnergyΛ
decomposition, freeEnergy = log 2 at β·J = 0,
mayerPartialSum_one_at_one) and §18.5 Mayer filter-connected /
ε^n / mayerPartialSum_analyticOnNhd now live in
`IsingModel.AmbientLattice.AnalyticityLambdaCapstones`. The earlier
import path is preserved by re-importing the new child.
-/


end Ambient
end IsingModel
