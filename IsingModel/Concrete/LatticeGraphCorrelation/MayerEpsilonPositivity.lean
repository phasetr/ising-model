import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaEpsilonIff

/-!
# ℤ^d positivity and vanishing of the nonempty-family activity sum

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the
characterisations of when the activity sum over the vertex-disjoint compatible polymer
families of the induced subgraph other than the empty one is strictly positive and of when it
vanishes: it is strictly positive exactly when the activity is strictly positive and that
subgraph has at least one polymer, and it vanishes exactly when the activity is `0` or that
subgraph has none. Each characterisation is given at a bare activity under `0 ≤ t` and at the
activity `tanh (β * J)` under `0 ≤ β * J`, with no sign condition on `β` or `J` separately.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: 0 < ε(t) ↔ 0 < t ∧ allPolymers ≠ ∅**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_pos_iff
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ↔
      0 < t ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_pos_iff
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: ε(t) = 0 ↔ t = 0 ∨ allPolymers = ∅**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_eq_zero_iff
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 ↔
      t = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅ :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_eq_zero_iff
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: 0 < ε(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅**. -/
theorem
vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_tanh_pos_iff
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_tanh_pos_iff
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: ε(tanh) = 0 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem
vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_tanh_eq_zero_iff
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅ :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_tanh_eq_zero_iff
    (IsingModel.latticeGraph d) Λ hβJ

end Ambient
end IsingModel
