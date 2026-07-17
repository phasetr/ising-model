import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete high-temperature expansion and bound wrappers for the lattice graph

Narrow child module for the §18.3-§18.4 high-temperature expansion,
lower/upper bound, sandwich, correlation, and deviation wrappers on
`latticeGraph d`. The theorem names are the same as the former
declarations, but callers can now import this child module directly.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff


/-! ## Moved: high-temperature partition-function and free-energy expansion wrappers

The §18.3-§18.4 high-temperature partition-function and free-energy
expansion / closed-form / lower-bound / upper-bound / `lower_le_upper`
wrappers on `latticeGraph d`, plus
`correlationΛ_latticeGraph_high_temp_h_zero_at_empty_A`, now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsExpansion`.
Sandwich and downstream wrappers continue to live in this module
(sharper-exp wrappers were further moved to `HighTemperatureBoundsExpSharper`
in PR #1935; deviation / continuity wrappers were further moved to
`HighTemperatureBoundsDeviation` in PR #1936; ratio_sandwich / ratio_bound
wrappers were further moved to `HighTemperatureBoundsRatioBounds` in
PR #1937). The earlier import path is preserved by re-importing the new
child.
-/


/-! ## Moved: FV (3.46) numerator and even-subgraph wrappers

The four ℤ^d Λ-level FV (3.46) wrappers
(`sum_high_temp_numerator_h_zero_odd_card_eq_zero_latticeGraph`,
`correlationΛ_latticeGraph_high_temp_h_zero_nonneg`,
`one_le_sum_pow_tanh_even_subgraph_latticeGraph`,
`high_temp_numerator_filter_eq_empty_of_odd_card_latticeGraph`) now
live in `HighTemperatureBoundsNumerator.lean`. -/


/-- **ℤ^d Z high-temp sandwich (FV (3.45))**: under `0 ≤ β·J`,
`2^|Λ| · cosh^|E_Λ| ≤ Z_Λ ≤ 2^(|Λ|+|E_Λ|) · cosh^|E_Λ|`. ℤ^d wrapper. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
    ∧ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ (Λ.card +
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) *
          Real.cosh (β * J) ^
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d freeEnergy high-temp sandwich (FV (3.45))**: under `0 < |Λ|`
and `0 ≤ β·J`,
`log 2 + (|E_Λ|/|Λ|) · log cosh(βJ) ≤ f_Λ ≤ log 2 + (|E_Λ|/|Λ|) · log(2·cosh βJ)`.
ℤ^d wrapper. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
          Λ.card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
    ∧ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
            Λ.card * Real.log (2 * Real.cosh (β * J)) :=
  freeEnergyΛ_high_temp_h_zero_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ hne


/-! ## Moved: correlationΛ pair / singleton basic wrappers at h = 0

The §18.3-§18.4 concrete `correlationΛ_latticeGraph` basic high-temperature
wrappers at `h = 0` (pair nonneg, pair `≤ 1`, singleton / pair trivial-slice
vanishings at `J = 0` and `β = 0`, pair sandwich, singleton / pair
ferromagnetic, singleton `= 0 ∧ ≤ 1`, pair+singleton bundle) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsCorrelationBasic`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: ℤ^d HT pair+singleton bundle wrappers

The 3 ℤ^d
`correlationΛ_latticeGraph_high_temp_h_zero_at_pair_singleton_*`
bundle wrappers (`_bundle_ferromagnetic`, `_complete_summary`,
`_trivial_slices_bundle`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsPairSingletonBundle`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: §18.7 high-temperature exponential decay capstones

The §18.7 high-temperature pair-correlation exponential-decay capstone
wrappers on `latticeGraph d` at `h = 0` (16 theorems drawn from five
capstone families `tanh_pow_dist` / `exp_rate_dist` /
`exp_highTempExpRate_dist` / `exp_alpha_dist` /
`exp_alpha_dist_of_le_highTempExpRate`, in their
`correlationΛ_latticeGraph` / `correlationAlongExhaustion_latticeGraph`
versions and the ferromagnetic variants that previously lived alongside
them; some named-rate / monotone-rate ferromagnetic variants of
`exp_highTempExpRate_dist` continue to live in
`Concrete/LatticeGraphCorrelation/CorrelationDecay.lean` and are
intentionally not moved) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsDecayCapstones`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: ℤ^d HT correlation pair / singleton wrappers

The 8 ℤ^d Λ-level correlation pair/singleton wrappers
(`correlationΛ_latticeGraph_high_temp_h_zero_at_pair_pos_of_edge`,
`_ferromagnetic`,
`_at_pair_ge_tanh_div_two_pow_edges`,
`_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic`,
`_at_pair_ge_tanh_div_two_pow_edges_of_latticeAdj`,
`_at_pair_pos_of_latticeAdj`, `_at_singleton`, `_odd_card_eq_zero`)
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsCorrelationPair`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: ℤ^d HT Λ-layer complete_summary wrappers

The 2 ℤ^d Λ-layer HT complete_summary wrappers
(`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_complete_summary`,
`freeEnergyΛ_latticeGraph_high_temp_h_zero_complete_summary`)
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsLambdaCompleteSummary`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: sharper-exp Z/f/log Z high-temperature bounds at h = 0

The §18.3-§18.4 concrete sharper-exp upper-bound / sandwich / complete-summary
wrappers on `latticeGraph d` at `h = 0` (17 theorems for
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_*_exp`,
`freeEnergyΛ_latticeGraph_high_temp_h_zero_*_exp`, and
`log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_*_exp` families,
with ferromagnetic variants) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsExpSharper`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: f/Z/log Z deviation / continuity wrappers at h = 0

The §18.3-§18.4 concrete deviation_bound / continuity_bundle /
deviation_sandwich / relative_sandwich / deviation_pos / pow_two_lt /
strict_deviation_bundle wrappers on `latticeGraph d` at `h = 0` (18 theorems
for `freeEnergyΛ_latticeGraph`, `partitionFunctionΛ_latticeGraph`, and
`log_partitionFunctionΛ_latticeGraph`, with ferromagnetic variants) now
live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsDeviation`.
The earlier import path is preserved by re-importing the new child.
-/



/-! ## Moved: Λ-level Z/f/log Z ratio sandwich and ratio bound wrappers

The §18.3-§18.4 concrete Λ-level `ratio_sandwich` / `ratio_bound`
wrappers on `latticeGraph d` at `h = 0` for
`partitionFunctionΛ_latticeGraph` (with `J = 0` / `β = 0` / `bundle`
variants plus ferromagnetic counterparts) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsRatioBounds`.
The 7 `triple_ratio_*` wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsTripleRatio`
(narrowed in PR #1998), and the 12 `log_partitionFunctionΛ_latticeGraph`
/ `freeEnergyΛ_latticeGraph` ratio wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsRatioLogFe`
(narrowed in PR #1999). The earlier import path is preserved by
re-importing all three children.
-/



/-! ## Moved: alongExhaustion correlation/sandwich basic wrappers at h = 0

The §18.3-§18.4 concrete alongExhaustion basic wrappers on `latticeGraph d`
at `h = 0` (25 theorems for `correlationAlongExhaustion_latticeGraph`
closed form, nonneg, sandwich, ferromagnetic, trivial-slice vanishings,
pair_sandwich, pair_singleton_bundle, pair_pos_of_edge,
singleton, odd_card_eq_zero; plus `partitionFunctionAlongExhaustion_latticeGraph`
and `freeEnergyAlongExhaustion_latticeGraph` sandwich; plus the high-temp
numerator filter helper) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionBasic`.
The two `_of_latticeAdj` along-exhaustion variants were narrowed in
PR #2074 into
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExCompleteSummary`
(see the next Moved block). The earlier import path is preserved by
re-importing the new child.
-/

/-! ## Moved: ℤ^d HT AlongExhaustion latticeAdj wrappers

The 2 ℤ^d along-exhaustion latticeAdj wrappers
(`correlationAlongExhaustion_latticeGraph_h_zero_at_pair_ge_tanh_div_two_pow_edges_of_latticeAdj`,
`correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_pos_of_latticeAdj`)
now live alongside the 2 along-exhaustion complete_summary wrappers in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExCompleteSummary`.
-/



/-! ## Moved: ℤ^d HT AlongExhaustion subset / even-subgraph wrappers

The 4 ℤ^d along-exhaustion HT wrappers
(`partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_subset_form`,
`one_le_sum_pow_tanh_even_subgraph_alongExhaustion_latticeGraph`,
`partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_closed_at_J_zero`,
`partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_closed_at_beta_zero`)
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExSubset`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: ℤ^d HT AlongExhaustion complete_summary wrappers

The 2 ℤ^d along-exhaustion complete_summary wrappers
(`partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_complete_summary`,
`freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_complete_summary`)
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExCompleteSummary`.
The earlier import path is preserved by re-importing the new child.
-/



/-! ## Moved: alongExhaustion sharper-exp Z/f/log Z wrappers at h = 0

The §18.3-§18.4 concrete alongExhaustion sharper-exp upper-bound /
sandwich / complete-summary wrappers on `latticeGraph d` at `h = 0`
(17 theorems for
`partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_*_exp`,
`freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_*_exp`, and
`log_partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_*_exp`
with ferromagnetic variants) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionExpSharper`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: alongExhaustion f/Z/log Z deviation / continuity wrappers

The §18.3-§18.4 concrete alongExhaustion deviation_bound_exp /
continuity_bundle / deviation_sandwich / relative_sandwich /
deviation_pos / pow_two_lt / strict_deviation_bundle wrappers on
`latticeGraph d` at `h = 0` (18 theorems for
`freeEnergyAlongExhaustion_latticeGraph`,
`partitionFunctionAlongExhaustion_latticeGraph`, and
`log_partitionFunctionAlongExhaustion_latticeGraph` with ferromagnetic
variants) live across two narrow children. The four
`freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_deviation_bound_exp`
/ `continuity_bundle` wrappers (with ferromagnetic variants) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExDeviationContinuity`.
The remaining wrappers still live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionDeviation`.
The earlier import path is preserved by re-importing both children.
-/


/-! ## Moved: alongExhaustion Z/f/log Z ratio sandwich/ratio bound wrappers

The §18.3-§18.4 concrete alongExhaustion ratio_sandwich_bundle /
ratio_bound wrappers on `latticeGraph d` at `h = 0` now live across
five narrow children, while the old umbrella
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionRatioBounds`
acts as a backwards-compat shim. The 2 `ratio_sandwich_bundle`
wrappers (general and ferromagnetic) live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExRatioSandwichBundle`
(carved out in PR #2089); the 4 J = 0 / β = 0 `ratio_bound` slice
wrappers (general and ferromagnetic) live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExRatioBoundSlices`
(carved out in PR #2090); the 2 `ratio_bound_bundle` wrappers (general
and ferromagnetic) live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExRatioBoundBundle`
(carved out in PR #2091); the 7 `triple_ratio_*` wrappers (sandwich +
bound bundles, J = 0 / β = 0 / ferromagnetic variants) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionTripleRatio`
(narrowed in PR #1996); and the 14 `log_partitionFunction` /
`freeEnergy` ratio wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionRatioLogFe`
(narrowed in PR #1997). The earlier import path is preserved by
re-importing all five children.
-/

/-! ## Moved: ℤ^d HT AlongExhaustion closed + lower-bound wrappers

The 4 ℤ^d along-exhaustion HT wrappers
(`partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_closed`,
`correlationAlongExhaustion_latticeGraph_high_temp_h_zero_nonneg`,
`partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_lower_bound`,
`freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_lower_bound`)
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExClosedLower`.
The earlier import path is preserved by re-importing the new child.
-/



/-! ## Moved: freeEnergyInfinite high-temperature wrappers

The §18.3-§18.4 concrete `freeEnergyInfinite` high-temperature wrappers
on `latticeGraph d` (with caller-supplied `Exhaustion` BED witness) and
on `cubicExhaustion d` (with the BED constant `c = d`) (10 theorems:
`upper_bound_exp_uniform`, `upper_bound_exp`, `sandwich_exp`,
`complete_summary_exp`, `deviation_bound_exp`,
`continuity_at_J_zero`, `continuity_at_beta_zero`, `continuity_bundle`,
`deviation_sandwich_exp`, `ratio_bound_bundle`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsFreeEnergyInfinite`.
The earlier import path is preserved by re-importing the new child.
-/

end Ambient
end IsingModel
