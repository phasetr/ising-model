import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Polymer free-energy ferromagnetic tanh-bound wrappers along an exhaustion

Narrow child module for the three §18.5 ambient alongExhaustion
ferromagnetic `polymerFreeEnergy_tanh_*_ferro` bound wrappers
extracted from `PolymerFreeEnergyTanhBounds.lean`:

* `polymerFreeEnergyAlongExhaustion_tanh_le_card_mul_ferro`
* `polymerFreeEnergyAlongExhaustion_tanh_sandwich_ferro`
* `polymerFreeEnergyAlongExhaustion_tanh_le_card_log_two_ferro`

Each wrapper is a thin pass-through to the corresponding ambient
`polymerFreeEnergy_Λ_tanh_*_ferromagnetic` lemma. Theorem names are
unchanged from the former `PolymerFreeEnergyTanhBounds` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: ferromagnetic polymerFreeEnergy_tanh ≤ |E|·tanh**. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_le_card_mul_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) :=
  polymerFreeEnergy_Λ_tanh_le_card_mul_ferromagnetic
    G (Λ.volume n) hJ hβ

/-- **Along-ex: ferromagnetic polymerFreeEnergy_tanh sandwich**. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_sandwich_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
          (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log (1 + Real.tanh (β * J)) :=
  polymerFreeEnergy_Λ_tanh_sandwich_ferromagnetic
    G (Λ.volume n) hJ hβ

/-- **Along-ex: ferromagnetic polymerFreeEnergy_tanh ≤ |E|·log 2**. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_le_card_log_two_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log 2 :=
  polymerFreeEnergy_Λ_tanh_le_card_log_two_ferro G (Λ.volume n) hJ hβ

end Ambient
end IsingModel
