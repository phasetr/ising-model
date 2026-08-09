import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerRecurrenceHasSum

/-!
# ℤ^d Mayer recurrence and the logarithmic series, along an exhaustion

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ`, the step recurrence between consecutive Mayer partial sums of the stage-`n`
induced subgraph and its rearrangement giving a Mayer expansion term as the difference of
consecutive partial sums; the alternating logarithmic series in the activity sum over the
vertex-disjoint compatible polymer families other than the empty one, which `HasSum`s to
`polymerFreeEnergy` whenever the absolute value of that sum is strictly below `1`, together
with the same conclusion holding eventually as the activity tends to `0`; and the convergence
of that activity sum to `0` as the activity tends to `0`. The recurrence statements assume
nothing about the activity, and the series statement carries its convergence hypothesis in the
activity sum itself rather than in the activity.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: mayerPartialSum recurrence** in `N`. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_succ
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (N : ℕ) (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (N + 1) t =
      IsingModel.mayerPartialSum
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N t +
        IsingModel.mayerExpansionTerm
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (N + 1) t :=
  Ambient.mayerPartialSumAlongExhaustion_succ
    (IsingModel.latticeGraph d) Λ N t n

/-- **ℤ^d along-ex: mayerExpansionTerm = mayerPartialSum diff**. -/
theorem
mayerExpansionTermAlongExhaustion_latticeGraph_eq_mayerPartialSum_diff
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (N : ℕ) (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (N + 1) t =
      IsingModel.mayerPartialSum
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (N + 1) t -
        IsingModel.mayerPartialSum
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N t :=
  Ambient.mayerExpansionTermAlongExhaustion_eq_mayerPartialSum_diff
    (IsingModel.latticeGraph d) Λ N t n

/-- **ℤ^d along-ex: polymerFreeEnergy hasSum via log under
`|ε(t)| < 1`**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_hasSum_via_log
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) {t : ℝ}
    (h_abs : |∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                        (inducedGraph (IsingModel.latticeGraph d)
                          (Λ.volume n))).erase ∅,
                ∏ P ∈ Γ, t ^ P.card| < 1) :
    HasSum (fun k : ℕ =>
        (-1 : ℝ) ^ k *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                    (inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) ^ (k + 1) /
          (k + 1))
      (IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t) :=
  Ambient.polymerFreeEnergyAlongExhaustion_hasSum_via_log
    (IsingModel.latticeGraph d) Λ n h_abs

/-- **ℤ^d along-ex: polymerFreeEnergy hasSum eventually as t → 0**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_hasSum_via_log_eventually
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    ∀ᶠ t : ℝ in nhds 0,
      HasSum (fun k : ℕ =>
          (-1 : ℝ) ^ k *
            (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                      (inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume n))).erase ∅,
                ∏ P ∈ Γ, t ^ P.card) ^ (k + 1) /
            (k + 1))
        (IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t) :=
  Ambient.polymerFreeEnergyAlongExhaustion_hasSum_via_log_eventually
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: ε(t) → 0 as t → 0**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_tendsto_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    Filter.Tendsto (fun t : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) (nhds 0) (nhds 0) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_tendsto_zero
    (IsingModel.latticeGraph d) Λ n

end Ambient
end IsingModel
