import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds

/-!
# ℤ^d Λ-layer polymerFreeEnergy tanh-bound ferromagnetic wrappers

Narrow child module for three ferromagnetic Λ-layer
`polymerFreeEnergy_Λ_latticeGraph_tanh_*_ferro` tanh-bound wrappers
extracted from `PolymerFreeEnergyTanhBounds.lean`:

* `polymerFreeEnergy_Λ_latticeGraph_tanh_le_card_mul_ferro`,
* `polymerFreeEnergy_Λ_latticeGraph_tanh_sandwich_ferro`,
* `polymerFreeEnergy_Λ_latticeGraph_tanh_le_card_log_two_ferro`.

Each result is a thin pass-through of the ambient
`Ambient.polymerFreeEnergy_Λ_tanh_*_ferromagnetic` /
`*_le_card_log_two_ferro` lemma at `G := IsingModel.latticeGraph d`.
The theorem names are unchanged from the former
`PolymerFreeEnergyTanhBounds` declarations.
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
