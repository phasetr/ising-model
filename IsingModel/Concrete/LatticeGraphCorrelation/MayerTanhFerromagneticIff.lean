import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaTanhFerroIff

/-!
# ℤ^d ferromagnetic sign characterisations of the polymer free energy

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the ferromagnetic
characterisations of `polymerFreeEnergy` at the activity `tanh (β * J)` against the activity
sum over the vertex-disjoint compatible polymer families of the induced subgraph other than
the empty one: the free energy is strictly below that sum exactly when the sum is strictly
positive, it vanishes exactly when the sum vanishes, and it is strictly positive exactly when
the sum is; and, unfolding those right-hand sides, it is strictly positive exactly when the
activity is strictly positive and the induced subgraph has at least one polymer, and it
vanishes exactly when the activity is `0` or that subgraph has none. Every statement here
assumes `0 ≤ β` and `0 ≤ J` separately, not merely `0 ≤ β * J`.
-/

namespace IsingModel
namespace Ambient

/-- **Z^d Λ: pFE(tanh) < eps(tanh) iff eps(tanh) > 0** (ferro). -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_lt_eps_iff_eps_pos_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
              ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  Ambient.polymerFreeEnergy_Λ_tanh_lt_eps_iff_eps_pos_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ

/-- **Z^d Λ: pFE(tanh) = 0 iff eps(tanh) = 0** (ferro). -/
theorem
polymerFreeEnergy_Λ_latticeGraph_tanh_eq_zero_iff_eps_eq_zero_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  Ambient.polymerFreeEnergy_Λ_tanh_eq_zero_iff_eps_eq_zero_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ

/-- **Z^d Λ: 0 < pFE(tanh) iff 0 < eps(tanh)** (ferro). -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_pos_iff_eps_pos_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    0 < IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  Ambient.polymerFreeEnergy_Λ_tanh_pos_iff_eps_pos_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ

/-- **Z^d Λ: 0 < pFE(tanh) iff 0 < tanh and allPolymers nonempty** (ferro). -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_pos_iff_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    0 < IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty :=
  Ambient.polymerFreeEnergy_Λ_tanh_pos_iff_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ

/-- **Z^d Λ: pFE(tanh) = 0 iff tanh = 0 or allPolymers empty** (ferro). -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_eq_zero_iff_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅ :=
  Ambient.polymerFreeEnergy_Λ_tanh_eq_zero_iff_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ

end Ambient
end IsingModel
