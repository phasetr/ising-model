import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayerRecurrenceEpsilon

/-!
# The Mayer recurrence and the logarithmic series for the polymer free energy

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Raising the truncation order by one adds the next Mayer expansion term to the Mayer partial
sum of the stage subgraph, and that term is equally the difference of two consecutive
partial sums.

Write `ε(t)` for the sum of `∏ P ∈ Γ, t ^ P.card` over the vertex-disjoint compatible
polymer families of the stage subgraph other than the empty family. Under `|ε(t)| < 1` the
alternating series `(-1) ^ k * ε(t) ^ (k + 1) / (k + 1)` sums to
`IsingModel.polymerFreeEnergy` of the stage subgraph at `t`; the same summability is stated
again for `t` in some neighbourhood of `0`. Finally `ε(t) → 0` as `t → 0`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: mayerPartialSum recurrence** in `N`. -/
theorem mayerPartialSumAlongExhaustion_succ
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n))
        (N + 1) t =
      IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n)) N t +
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) (N + 1) t :=
  mayerPartialSum_Λ_succ G (Λ.volume n) N t

/-- **Along-ex: mayerExpansionTerm = mayerPartialSum diff**. -/
theorem mayerExpansionTermAlongExhaustion_eq_mayerPartialSum_diff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) (N + 1) t =
      IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) (N + 1) t -
        IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n)) N t :=
  mayerExpansionTerm_Λ_eq_mayerPartialSum_diff G (Λ.volume n) N t

/-- **Along-ex: polymerFreeEnergy hasSum via log under `|ε(t)| < 1`**. -/
theorem polymerFreeEnergyAlongExhaustion_hasSum_via_log
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) {t : ℝ}
    (h_abs : |∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                        (inducedGraph G (Λ.volume n))).erase ∅,
                ∏ P ∈ Γ, t ^ P.card| < 1) :
    HasSum (fun k : ℕ =>
        (-1 : ℝ) ^ k *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                    (inducedGraph G (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) ^ (k + 1) /
          (k + 1))
      (IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t) :=
  polymerFreeEnergy_Λ_hasSum_via_log G (Λ.volume n) h_abs

/-- **Along-ex: polymerFreeEnergy hasSum eventually as `t → 0`**. -/
theorem polymerFreeEnergyAlongExhaustion_hasSum_via_log_eventually
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    ∀ᶠ t : ℝ in nhds 0,
      HasSum (fun k : ℕ =>
          (-1 : ℝ) ^ k *
            (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                      (inducedGraph G (Λ.volume n))).erase ∅,
                ∏ P ∈ Γ, t ^ P.card) ^ (k + 1) /
            (k + 1))
        (IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t) :=
  polymerFreeEnergy_Λ_hasSum_via_log_eventually G (Λ.volume n)

/-- **Along-ex: ε(t) → 0 as t → 0**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_tendsto_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Filter.Tendsto (fun t : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) (nhds 0) (nhds 0) :=
  vdPolymerFamilies_sum_Λ_minus_one_tendsto_zero G (Λ.volume n)

end Ambient
end IsingModel
