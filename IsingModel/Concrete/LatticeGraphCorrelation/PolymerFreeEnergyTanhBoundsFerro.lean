import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds

/-!
# ℤ^d Λ ferromagnetic polymerFreeEnergy tanh bounds (§18.5)

Instantiates at fixed volume `Λ` on `IsingModel.latticeGraph d` the ferromagnetic form of the
polymer free-energy estimates at activity `tanh (β * J)` — the ceilings `|E| * tanh (β * J)`
and `|E| * log 2`, and the sandwich between `0` and `|E| * log (1 + tanh (β * J))` — stated
under the ferromagnetic hypotheses `0 ≤ J` and `0 < β`. These are the ℤ^d ferromagnetic
high-temperature bounds of the GJ §18.5 cluster expansion.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: ferro polymerFreeEnergy_tanh ≤ |E|·tanh**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_le_card_mul_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.tanh (β * J) :=
  Ambient.polymerFreeEnergy_Λ_tanh_le_card_mul_ferromagnetic
    (IsingModel.latticeGraph d) Λ hJ hβ

/-- **ℤ^d Λ: ferro polymerFreeEnergy_tanh sandwich**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_sandwich_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    0 ≤ IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.log (1 + Real.tanh (β * J)) :=
  Ambient.polymerFreeEnergy_Λ_tanh_sandwich_ferromagnetic
    (IsingModel.latticeGraph d) Λ hJ hβ

/-- **ℤ^d Λ: ferro polymerFreeEnergy_tanh ≤ |E|·log 2**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_le_card_log_two_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.log 2 :=
  Ambient.polymerFreeEnergy_Λ_tanh_le_card_log_two_ferro
    (IsingModel.latticeGraph d) Λ hJ hβ

end Ambient
end IsingModel
