import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhBoundsFerro

/-!
# Concrete along-ex ferromagnetic polymerFreeEnergy tanh-bound wrappers

Narrow child module for 3 ℤ^d along-exhaustion ferromagnetic
`polymerFreeEnergyAlongExhaustion_*_tanh_*_ferro` wrappers extracted
from `PolymerFreeEnergyTanhBoundsAlongEx.lean`:

* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_le_card_mul_ferro`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_sandwich_ferro`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_le_card_log_two_ferro`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.polymerFreeEnergyAlongExhaustion_tanh_*_ferro` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `PolymerFreeEnergyTanhBoundsAlongEx` declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d along-ex: ferro polymerFreeEnergy_tanh ≤ |E|·tanh**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_le_card_mul_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n)).edgeFinset.card * Real.tanh (β * J) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_le_card_mul_ferro
    (IsingModel.latticeGraph d) Λ hJ hβ n

/-- **ℤ^d along-ex: ferro polymerFreeEnergy_tanh sandwich**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_sandwich_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n)).edgeFinset.card *
        Real.log (1 + Real.tanh (β * J)) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_sandwich_ferro
    (IsingModel.latticeGraph d) Λ hJ hβ n

/-- **ℤ^d along-ex: ferro polymerFreeEnergy_tanh ≤ |E|·log 2**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_le_card_log_two_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n)).edgeFinset.card * Real.log 2 :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_le_card_log_two_ferro
    (IsingModel.latticeGraph d) Λ hJ hβ n

end Ambient
end IsingModel
