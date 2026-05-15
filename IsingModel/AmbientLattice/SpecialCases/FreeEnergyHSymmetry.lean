import IsingModel.AmbientLattice.SpontaneousMono

/-!
# Free-energy `h`-symmetry / `|h|`-monotonicity along an exhaustion

Narrow child module for three along-exhaustion `freeEnergyAlongExhaustion`
`h`-symmetry / `|h|`-monotonicity wrappers extracted from
`FreeEnergy.lean`. Each wrapper is a thin pass-through to the
corresponding `IsingModel.freeEnergy_*` ambient lemma via
`change` + `exact`. Theorem names are unchanged from the former
`FreeEnergy` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion h-evenness**:
`freeEnergyAlongExhaustion G Λ ⟨J, -h, β⟩ n = freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n`. -/
theorem freeEnergyAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, -h, β⟩ : IsingParams ℝ)
    = IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
        (⟨J, h, β⟩ : IsingParams ℝ)
  exact IsingModel.freeEnergy_neg_h _ J h β

/-- **Along-exhaustion `|h|`-rewrite**:
`freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n = freeEnergyAlongExhaustion G Λ ⟨J, |h|, β⟩ n`. -/
theorem freeEnergyAlongExhaustion_eq_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, h, β⟩ : IsingParams ℝ)
    = IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
        (⟨J, |h|, β⟩ : IsingParams ℝ)
  exact IsingModel.freeEnergy_eq_abs_h _ J h β

/-- **Along-exhaustion ferromagnetic `|h|`-monotonicity**:
for `J ≥ 0`, `β > 0` and any real `h₁, h₂` with `|h₁| ≤ |h₂|`,
`freeEnergyAlongExhaustion G Λ ⟨J, h₁, β⟩ n ≤ freeEnergyAlongExhaustion G Λ ⟨J, h₂, β⟩ n`. -/
theorem freeEnergyAlongExhaustion_monotone_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ freeEnergyAlongExhaustion G Λ (⟨J, h₂, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, h₁, β⟩ : IsingParams ℝ)
    ≤ IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
        (⟨J, h₂, β⟩ : IsingParams ℝ)
  exact IsingModel.freeEnergy_monotone_abs_h _ J β hJ hβ hh

end Ambient
end IsingModel
