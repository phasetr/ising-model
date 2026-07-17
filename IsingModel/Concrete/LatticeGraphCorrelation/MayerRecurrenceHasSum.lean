import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerRecurrenceEpsilon

/-!
# Concrete Mayer recurrence and polymer free-energy HasSum wrappers

Narrow child module for concrete `ℤ^d` Mayer recurrence wrappers,
`polymerFreeEnergy` log-series `HasSum` wrappers, and the
`vdPolymerFamilies_sum - 1` tendsto-zero wrapper. This keeps callers that only
need these forwarders out of the monolithic lattice-correlation module.
-/

namespace IsingModel
namespace Ambient

/-! ### §18.5 Mayer recurrence + hasSum + tendsto ℤ^d wraps -/

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

/-! ## Moved: AlongExhaustion mayer recurrence / hasSum wrappers

The five AlongExhaustion mayer recurrence / hasSum wrappers
(`mayerPartialSumAlongExhaustion_latticeGraph_succ`,
`mayerExpansionTermAlongExhaustion_latticeGraph_eq_mayerPartialSum_diff`,
`polymerFreeEnergyAlongExhaustion_latticeGraph_hasSum_via_log`,
`polymerFreeEnergyAlongExhaustion_latticeGraph_hasSum_via_log_eventually`,
`vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_tendsto_zero`)
now live in `MayerRecurrenceHasSumAlongEx.lean`. -/



end Ambient
end IsingModel
