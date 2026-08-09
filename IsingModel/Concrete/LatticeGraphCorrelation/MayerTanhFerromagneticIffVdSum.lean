import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaTanhFerroIff

/-!
# ℤ^d ferromagnetic activity-sum thresholds and strict free-energy bounds

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, at the activity
`tanh (β * J)`, the ferromagnetic thresholds for the activity sum over the vertex-disjoint
compatible polymer families of the induced subgraph — it exceeds `1` exactly when the activity
is strictly positive and that subgraph has at least one polymer, and it equals `1` exactly
when the activity is `0` or that subgraph has none — together with strict upper bounds on
`polymerFreeEnergy`, by `(1 + tanh (β * J)) ^ |E_Λ| - 1` and by the activity sum over the
families other than the empty one. Every statement assumes `0 ≤ β` and `0 ≤ J` separately; the
strict upper bounds assume in addition that the latter sum is strictly positive.
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
