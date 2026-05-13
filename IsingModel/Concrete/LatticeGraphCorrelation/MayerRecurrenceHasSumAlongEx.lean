import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerRecurrenceHasSum

/-!
# ℤ^d AlongExhaustion mayer recurrence / hasSum wrappers

Narrow child module for five ℤ^d AlongExhaustion mayer recurrence /
hasSum wrappers extracted from `MayerRecurrenceHasSum.lean`:

* `mayerPartialSumAlongExhaustion_latticeGraph_succ`,
* `mayerExpansionTermAlongExhaustion_latticeGraph_eq_mayerPartialSum_diff`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_hasSum_via_log`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_hasSum_via_log_eventually`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_tendsto_zero`.
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
