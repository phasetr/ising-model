import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBounds
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsTripleRatio
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFe
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionClosedForms
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicPairBase

/-!
# Ambient alongExhaustion correlation pair sandwich wrappers at h = 0

Narrow child module for the four §18.3-§18.4 ambient alongExhaustion
correlation pair sandwich/bound wrappers extracted from
`HighTemperatureBoundsCorrelationBasic.lean`:

* `correlationAlongExhaustion_high_temp_h_zero_at_pair_le_one`
* `correlationAlongExhaustion_high_temp_h_zero_at_pair_nonneg`
* `correlationAlongExhaustion_high_temp_h_zero_at_pair_sandwich`
* `correlationAlongExhaustion_high_temp_h_zero_at_pair_ferromagnetic`

Internal dependencies (`_sandwich` → `_nonneg` + `_le_one`,
`_ferromagnetic` → `_sandwich`) stay inside this module. External
dependencies on `correlationAlongExhaustion_high_temp_h_zero_nonneg`
and `correlationΛ_le_one` are provided by the inherited imports.
Theorem names are unchanged from the former
`HighTemperatureBoundsCorrelationBasic` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ## Moved: 2 base pair wrappers

The two base pair wrappers
(`correlationAlongExhaustion_high_temp_h_zero_at_pair_le_one`,
`correlationAlongExhaustion_high_temp_h_zero_at_pair_nonneg`) now
live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicPairBase`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

/-- **Along-ex pair sandwich at h = 0**: under `0 ≤ β·J`,
`0 ≤ correlationAlongExhaustion G Λ ⟨J, 0, β⟩ {i, j} n ≤ 1`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : V) (n : ℕ) :
    0 ≤ correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ≤ 1 :=
  ⟨correlationAlongExhaustion_high_temp_h_zero_at_pair_nonneg G Λ J β hβJ i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_le_one G Λ J β i j n⟩

/-- **Along-ex pair ferromagnetic sandwich at h = 0**: under `0 ≤ J, 0 < β`,
`0 ≤ correlationAlongExhaustion ⟨J,0,β⟩ {i,j} n ≤ 1`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : V) (n : ℕ) :
    0 ≤ correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ≤ 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_sandwich
    G Λ J β (mul_nonneg hβ.le hJ) i j n

/-! ## Moved: 2 trivial-slice pair vanishing wrappers

The two trivial-parameter-slice vanishing identities
(`correlationAlongExhaustion_high_temp_h_zero_at_pair_J_zero`,
`correlationAlongExhaustion_high_temp_h_zero_at_pair_beta_zero`)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicPairTrivial`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient

end IsingModel
