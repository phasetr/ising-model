import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrictZ

/-!
# Ambient alongExhaustion ferromagnetic Z / log Z strict-deviation wrappers at h = 0

Narrow child module for the two §18.3-§18.4 ambient alongExhaustion
ferromagnetic `partitionFunction` / `log_partitionFunction`
strict-deviation wrappers extracted from
`HighTemperatureBoundsDeviationStrictFerro.lean`:

* `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt_ferromagnetic`
* `log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_pos_ferromagnetic`

Each wrapper derives `0 < β * J` from `0 < J` and `0 < β` and
forwards to the corresponding general non-ferromagnetic wrapper
(in `HighTemperatureBoundsDeviationStrictZ`). Theorem names are
unchanged from the former `HighTemperatureBoundsDeviation`
declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic Z strict deviation at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (n : ℕ)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    (2 : ℝ) ^ (Λ.volume n).card
      < partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt
    G Λ J β (mul_pos hβ hJ) n hEpos

/-- **Along-ex ferromagnetic log Z strict deviation at stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_pos_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (n : ℕ)
    (hEpos : 0 < (inducedGraph G (Λ.volume n)).edgeFinset.card) :
    0 < Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - ((Λ.volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_pos
    G Λ J β (mul_pos hβ hJ) n hEpos

end Ambient
end IsingModel
