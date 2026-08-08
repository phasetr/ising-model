import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhBoundsFerro

/-!
# ℤ^d AlongExhaustion ferromagnetic polymerFreeEnergy tanh bounds (§18.5)

Instantiates along an exhaustion at `IsingModel.latticeGraph d` the ferromagnetic form of the
polymer free-energy estimates at activity `tanh (β * J)` — the ceilings `|E| * tanh (β * J)`
and `|E| * log 2`, and the sandwich between `0` and `|E| * log (1 + tanh (β * J))` — stated
under the ferromagnetic hypotheses `0 ≤ J` and `0 < β`. These are the ℤ^d ferromagnetic
high-temperature bounds of the GJ §18.5 cluster expansion.
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
