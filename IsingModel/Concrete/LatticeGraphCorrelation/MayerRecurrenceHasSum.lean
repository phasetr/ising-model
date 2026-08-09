import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerRecurrenceEpsilon

/-!
# ℤ^d Mayer recurrence and the logarithmic series for the polymer free energy

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the step recurrence
between consecutive Mayer partial sums of the induced subgraph and its rearrangement giving a
Mayer expansion term as the difference of consecutive partial sums; the alternating
logarithmic series in the activity sum over the vertex-disjoint compatible polymer families
other than the empty one, which `HasSum`s to `polymerFreeEnergy` whenever the absolute value
of that sum is strictly below `1`, together with the same conclusion holding eventually as the
activity tends to `0`; and the convergence of that activity sum to `0` as the activity tends
to `0`. The recurrence statements assume nothing about the activity, and the series statement
carries its convergence hypothesis in the activity sum itself rather than in the activity.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: mayerPartialSum recurrence** in `N`. -/
theorem mayerPartialSum_Λ_latticeGraph_succ
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (t : ℝ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) (N + 1) t =
      IsingModel.mayerPartialSum
          (inducedGraph (IsingModel.latticeGraph d) Λ) N t +
        IsingModel.mayerExpansionTerm
          (inducedGraph (IsingModel.latticeGraph d) Λ) (N + 1) t :=
  Ambient.mayerPartialSum_Λ_succ (IsingModel.latticeGraph d) Λ N t

/-- **ℤ^d Λ: mayerExpansionTerm = mayerPartialSum diff**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_eq_mayerPartialSum_diff
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (t : ℝ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) (N + 1) t =
      IsingModel.mayerPartialSum
          (inducedGraph (IsingModel.latticeGraph d) Λ) (N + 1) t -
        IsingModel.mayerPartialSum
          (inducedGraph (IsingModel.latticeGraph d) Λ) N t :=
  Ambient.mayerExpansionTerm_Λ_eq_mayerPartialSum_diff
    (IsingModel.latticeGraph d) Λ N t

/-- **ℤ^d Λ: polymerFreeEnergy hasSum via log under `|ε(t)| < 1`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_hasSum_via_log
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ}
    (h_abs : |∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                        (inducedGraph (IsingModel.latticeGraph d)
                          Λ)).erase ∅,
                ∏ P ∈ Γ, t ^ P.card| < 1) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                    (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
          (n + 1))
      (IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t) :=
  Ambient.polymerFreeEnergy_Λ_hasSum_via_log
    (IsingModel.latticeGraph d) Λ h_abs

/-- **ℤ^d Λ: polymerFreeEnergy hasSum eventually as `t → 0`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_hasSum_via_log_eventually
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    ∀ᶠ t : ℝ in nhds 0,
      HasSum (fun n : ℕ =>
          (-1 : ℝ) ^ n *
            (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                      (inducedGraph (IsingModel.latticeGraph d)
                        Λ)).erase ∅,
                ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
            (n + 1))
        (IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) Λ) t) :=
  Ambient.polymerFreeEnergy_Λ_hasSum_via_log_eventually
    (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: ε(t) → 0 as t → 0**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_tendsto_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    Filter.Tendsto (fun t : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) (nhds 0) (nhds 0) :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_tendsto_zero
    (IsingModel.latticeGraph d) Λ

end Ambient
end IsingModel
