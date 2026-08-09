import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaEpsilonIff

/-!
# ℤ^d strict polymer bounds at the `tanh` activity and strict monotonicity

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the strict
statements available once the induced subgraph has at least one polymer: at the activity
`tanh (β * J)` the activity sum over the vertex-disjoint compatible polymer families exceeds
`1`, and the sum over the families other than the empty one is strictly positive, each under
`0 < tanh (β * J)`; and `polymerFreeEnergy` and that activity sum are each
`StrictMonoOn (Set.Ioi 0)`, with no hypothesis beyond the nonempty polymer set.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: 1 < vdSum(tanh) under `0 < tanh` and polymers
exist**. -/
theorem
vdPolymerFamilies_sum_Λ_latticeGraph_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J))
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  Ambient.vdPolymerFamilies_sum_Λ_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_tanh_pos h_poly

/-- **ℤ^d Λ: 0 < ε(tanh) under `0 < tanh` and polymers exist**. -/
theorem
vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J))
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_tanh_pos h_poly

/-- **ℤ^d Λ: pFE is `StrictMonoOn (Set.Ioi 0)`**. -/
theorem
polymerFreeEnergy_Λ_latticeGraph_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty) :
    StrictMonoOn (fun t : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t) (Set.Ioi 0) :=
  Ambient.polymerFreeEnergy_Λ_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_poly

/-- **ℤ^d Λ: vdSum is `StrictMonoOn (Set.Ioi 0)`**. -/
theorem
vdPolymerFamilies_sum_Λ_latticeGraph_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ioi 0) :=
  Ambient.vdPolymerFamilies_sum_Λ_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_poly

end Ambient
end IsingModel
