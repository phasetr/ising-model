import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionClosedForms
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionVariants
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperFerro
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperComplete
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperCompleteFerro
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperSandwich
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationFerro
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationContinuity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrict
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrictFerro
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBounds
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsBound
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsTripleRatio
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFe
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeFreeEnergyBoundOnly
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeLogBound
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstones
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasic
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicSingletonBundle
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicPair
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelation

/-!
# High-temperature expansion and bound wrappers along an exhaustion

Narrow child module for the §18.3-§18.4 high-temperature expansion,
lower/upper bound, sandwich, correlation, and deviation wrappers along an
exhaustion. The theorem names are the same as the former declarations,
but callers can now avoid importing the monolithic special-cases original module.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]


/-! ## Moved: alongExhaustion partition/free-energy expansion wrappers

The §18.3-§18.4 ambient alongExhaustion partition function / free energy
expansion / closed-form / lower-bound / upper-bound / sandwich /
complete-summary wrappers (20 theorems for
`partitionFunctionAlongExhaustion`, `freeEnergyAlongExhaustion`,
`log_partitionFunctionAlongExhaustion`, `correlationAlongExhaustion` closed
forms, plus the `one_le_sum_pow_tanh_even_subgraph_alongExhaustion` helper)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: alongExhaustion sharper-exp Z/f/log Z wrappers

The §18.3-§18.4 ambient alongExhaustion sharper-exp upper-bound /
sandwich / complete-summary wrappers (16 theorems for
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_*_exp`,
`freeEnergyAlongExhaustion_high_temp_h_zero_*_exp`, and
`log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_*_exp`
with ferromagnetic variants) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: alongExhaustion f/Z/log Z deviation / continuity wrappers

The §18.3-§18.4 ambient alongExhaustion deviation_bound_exp /
deviation_sandwich / relative_sandwich / deviation_pos / pow_two_lt /
strict_deviation_bundle wrappers (20 theorems for
`freeEnergyAlongExhaustion`, `partitionFunctionAlongExhaustion`, and
`log_partitionFunctionAlongExhaustion` with ferromagnetic variants)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation`,
with the 4 `freeEnergyAlongExhaustion_*_continuity_*` wrappers
(`_at_J_zero`, `_at_beta_zero`, `_bundle`, `_bundle_ferromagnetic`)
subsequently narrowed in PR #2024 into
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationContinuity`.
The earlier import path is preserved by re-importing both children.
-/

/-! ## Moved: alongExhaustion Z/f/log Z ratio sandwich/ratio bound wrappers

The §18.3-§18.4 ambient alongExhaustion `partitionFunctionAlongExhaustion`
`ratio_sandwich` / `ratio_bound` wrappers (with bundle / `_of_nonempty`
variants plus ferromagnetic counterparts) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBounds`.
The 12 `log_partitionFunctionAlongExhaustion` and
`freeEnergyAlongExhaustion` ratio_sandwich / ratio_bound (+
deviation_pos / pow_two_lt) wrappers now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFe`
(narrowed in PR #1995). The 2 `triple_ratio_sandwich_bundle` wrappers
(J = 0 / β = 0 trivial slices) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsTripleRatio`
(narrowed in PR #1994; the bound-bundle and ferromagnetic variants were
dropped in PR #4676). The earlier import path is preserved by
re-importing all three children.
-/


/-- **Along-exhaustion freeEnergy high-temp sandwich (FV (3.45))**: under
`0 ≤ β·J` and `0 < |Λ_n|`, at every stage `n`,
`log 2 + (|E_n|/|Λ_n|) log cosh(βJ) ≤ f_n ≤ log 2 + (|E_n|/|Λ_n|) log(2·cosh βJ)`. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
    ∧ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2
        + ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
            (Λ.volume n).card * Real.log (2 * Real.cosh (β * J)) :=
  ⟨freeEnergyAlongExhaustion_high_temp_h_zero_lower_bound G Λ J β hβJ n hne,
   freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound G Λ J β hβJ n hne⟩

/-- **Along-exhaustion FV (3.46) numerator filter empty for odd `|A|`**:
at every stage `n`, for any `A : Finset ↑(Λ.volume n)` of odd cardinality,
the FV (3.46) numerator filter set is *literally empty*.
Per-stage application of `high_temp_numerator_filter_eq_empty_of_odd_card_Λ`
(Step 299), via the edge-vertex handshake. -/
theorem high_temp_numerator_filter_eq_empty_of_odd_card_alongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (A : Finset ↑(Λ.volume n)) (hA_odd : Odd A.card) :
    (inducedGraph G (Λ.volume n)).edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ↑(Λ.volume n)) => ∀ v : ↑(Λ.volume n),
          Even ((if v ∈ A then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)) = ∅ :=
  high_temp_numerator_filter_eq_empty_of_odd_card_Λ G (Λ.volume n) A hA_odd

-- `correlationAlongExhaustion_high_temp_h_zero_odd_card_eq_zero` moved
-- into `HighTemperatureBoundsCorrelationBasic.lean` (PR #2001) because
-- the singleton wrappers there depend on it.

/-! ## Moved: correlation basic + bundle wrappers

The 15 ambient alongExhaustion §18.3-§18.4 correlation basic /
bundle wrappers (`correlationAlongExhaustion_high_temp_h_zero_at_*`)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasic`.
The earlier import path is preserved by re-importing the new child
via the umbrella.
-/

/-! ## Moved: §18.7 decay capstone wrappers

The 11 ambient alongExhaustion §18.7 high-temperature exponential
decay capstone wrappers (pair correlation `tanh_pow_dist` /
`exp_rate_dist` / `exp_highTempExpRate_dist` / `exp_alpha_dist` /
`pos_of_edge` / `ge_tanh_div_two_pow_edges`, with ferromagnetic
variants) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstones`.
The earlier import path is preserved by re-importing the new child
via the umbrella.
-/


/-! ## Moved: 2 umbrella-residue correlation wrappers

The two umbrella-residue correlation wrappers
(`correlationAlongExhaustion_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges`,
`correlationAlongExhaustion_high_temp_h_zero_at_singleton_ferromagnetic`)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelation`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
