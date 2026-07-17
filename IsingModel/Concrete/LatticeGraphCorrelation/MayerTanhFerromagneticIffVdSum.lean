import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaTanhFerroIff

/-!
# ℤ^d Mayer tanh-ferromagnetic vdSum iff and pFE-comparison wrappers

Narrow child module for four Λ-layer ℤ^d Mayer tanh-ferromagnetic
wrappers extracted from `MayerTanhFerromagneticIff.lean`:

* `vdPolymerFamilies_sum_Λ_latticeGraph_tanh_gt_one_iff_ferro`,
* `vdPolymerFamilies_sum_Λ_latticeGraph_tanh_eq_one_iff_ferro`,
* `polymerFreeEnergy_Λ_latticeGraph_tanh_lt_pow_sub_one_of_eps_pos_ferro`,
* `polymerFreeEnergy_Λ_latticeGraph_tanh_lt_eps_of_eps_pos_ferro`.

Each result is a thin pass-through of the ambient
`Ambient.vdPolymerFamilies_sum_Λ_tanh_*` /
`Ambient.polymerFreeEnergy_Λ_tanh_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `MayerTanhFerromagneticIff` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **Z^d Λ: 1 < vdSum(tanh) iff 0 < tanh and allPolymers nonempty** (ferro). -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_tanh_gt_one_iff_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty :=
  Ambient.vdPolymerFamilies_sum_Λ_tanh_gt_one_iff_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ

/-- **Z^d Λ: vdSum(tanh) = 1 iff tanh = 0 or allPolymers empty** (ferro). -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_tanh_eq_one_iff_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅ :=
  Ambient.vdPolymerFamilies_sum_Λ_tanh_eq_one_iff_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ

/-- **Z^d Λ: pFE(tanh) < (1+tanh)^|E| - 1** under eps(tanh) > 0
(ferro). -/
theorem
polymerFreeEnergy_Λ_latticeGraph_tanh_lt_pow_sub_one_of_eps_pos_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card -
        1 :=
  Ambient.polymerFreeEnergy_Λ_tanh_lt_pow_sub_one_of_eps_pos_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ h_eps_pos

/-- **Z^d Λ: pFE(tanh) < eps(tanh)** under eps(tanh) > 0 (ferro). -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_lt_eps_of_eps_pos_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  Ambient.polymerFreeEnergy_Λ_tanh_lt_eps_of_eps_pos_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ h_eps_pos

end Ambient
end IsingModel
