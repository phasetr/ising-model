import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient alongExhaustion ferromagnetic freeEnergy ratio_bound non-bundle wrappers at h = 0

Narrow child module for the two §18.3-§18.4 ambient alongExhaustion
ferromagnetic
`freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound*_ferromagnetic`
non-bundle wrappers extracted from
`HighTemperatureBoundsRatioLogFeFreeEnergyBoundOnly.lean`:

* `freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_ferromagnetic`
  (J = 0 trivial slice, ferromagnetic specialisation)
* `freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_beta_zero_ferromagnetic`
  (β = 0 trivial slice, ferromagnetic specialisation)

To avoid an import cycle, the proofs inline the same
`freeEnergyΛ_high_temp_h_zero_ratio_bound*` ambient lemma the
non-ferromagnetic siblings call, derived under
`mul_nonneg hβ.le hJ`. Theorem names are unchanged from the former
`HighTemperatureBoundsRatioLogFeFreeEnergyBound` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic f ratio bound at J=0**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card := by
  change freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
      - freeEnergyΛ G (Λ.volume n) (⟨0, 0, β⟩ : IsingParams ℝ) ≤ _
  exact freeEnergyΛ_high_temp_h_zero_ratio_bound
    G (Λ.volume n) J β (mul_nonneg hβ.le hJ) hne

/-- **Along-ex ferromagnetic f ratio bound at β=0**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_beta_zero_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card := by
  change freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
      - freeEnergyΛ G (Λ.volume n) (⟨J, 0, 0⟩ : IsingParams ℝ) ≤ _
  exact freeEnergyΛ_high_temp_h_zero_ratio_bound_beta_zero
    G (Λ.volume n) J β (mul_nonneg hβ.le hJ) hne

end Ambient

end IsingModel
