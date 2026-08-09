import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaEpsilonIff

/-!
# ℤ^d strict monotonicity and strict positivity of the polymer activity sum

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the strict
behaviour of the activity sum over the vertex-disjoint compatible polymer families of the
induced subgraph once that subgraph has at least one polymer: the sum strictly increases from
activity `s` to activity `t`, it is `StrictMonoOn (Set.Ici 0)`, it exceeds `1` at a strictly
positive activity, and the corresponding sum over the families other than the empty one is
strictly positive there. Every statement here assumes that the polymer set is nonempty. Beyond
that, the pointwise increase assumes `0 ≤ s` and `s < t`, the statements at a single activity
assume `0 < t`, and the `StrictMonoOn` statement assumes nothing further.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: vdSum(s) < vdSum(t) under polymers exist**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_lt_of_lt_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, s ^ P.card) <
      ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sum_Λ_lt_of_lt_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_poly hs hst

/-- **ℤ^d Λ: vdSum is `StrictMonoOn (Set.Ici 0)`**. -/
theorem
vdPolymerFamilies_sum_Λ_latticeGraph_strictMonoOn_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  Ambient.vdPolymerFamilies_sum_Λ_strictMonoOn_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_poly

/-- **ℤ^d Λ: 1 < vdSum under `0 < t` and polymers exist**. -/
theorem
vdPolymerFamilies_sum_Λ_latticeGraph_gt_one_of_t_pos_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
            ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.vdPolymerFamilies_sum_Λ_gt_one_of_t_pos_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_t_pos h_poly

/-- **ℤ^d Λ: 0 < ε(t) under `0 < t` and polymers exist**. -/
theorem
vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_pos_of_t_pos_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_pos_of_t_pos_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_t_pos h_poly

end Ambient
end IsingModel
