import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsSingletons

/-!
# Ambient alongExhaustion ferromagnetic Z ratio_bound non-bundle wrappers at h = 0

Narrow child module for the two §18.3-§18.4 ambient alongExhaustion
ferromagnetic
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound*_ferromagnetic`
non-bundle wrappers extracted from
`HighTemperatureBoundsRatioBoundsBoundOnly.lean`:

* `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_ferromagnetic`
  (J = 0 trivial slice, ferromagnetic specialisation)
* `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero_ferromagnetic`
  (β = 0 trivial slice, ferromagnetic specialisation)

To avoid an import cycle, the proofs inline the same
`.2`-projection-of-`_ratio_sandwich*` construction the
non-ferromagnetic siblings use, derived under `mul_nonneg hβ.le hJ`.
Theorem names are unchanged from the former
`HighTemperatureBoundsRatioBoundsBound` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic Z ratio upper bound at J=0, stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) :=
  (partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich
    G Λ J β (mul_nonneg hβ.le hJ) n).2

/-- **Along-ex ferromagnetic Z ratio upper bound at β=0, stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
      ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) :=
  (partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    G Λ J β (mul_nonneg hβ.le hJ) n).2

end Ambient

end IsingModel
