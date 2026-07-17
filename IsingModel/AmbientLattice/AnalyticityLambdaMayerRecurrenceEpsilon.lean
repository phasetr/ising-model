import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.MayerCore.LogTaylor

/-!
# AmbientLattice/Analyticity Mayer recurrence + ε infrastructure wrappers

Narrow child module for 12 §18.5 Λ-layer wrappers covering Mayer
recurrence (`mayerPartialSum_Λ_succ`,
`mayerExpansionTerm_Λ_eq_mayerPartialSum_diff`),
`polymerFreeEnergy_Λ_hasSum_via_log` / `_hasSum_via_log_eventually`,
`vdPolymerFamilies_sum_Λ_minus_one_tendsto_zero`, Mayer term sign at
`n = 1, 2` (`mayerExpansionTerm_Λ_one_nonneg_of_nonneg`,
`_two_nonpos_of_nonneg`), `vdPolymerFamilies_sum_Λ_minus_one_{at_zero,
continuous, analyticAt, lt_one_eventually}`, and
`allPolymers_Λ_eq_empty_of_edgeFinset_empty`. The theorem names are
unchanged from the former `Analyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 Mayer recurrence + hasSum + tendsto Λ-layer wraps -/

/-- **Λ-layer: mayerPartialSum recurrence** in `N`. -/
theorem mayerPartialSum_Λ_succ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) (N + 1) t =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N t +
        IsingModel.mayerExpansionTerm (inducedGraph G Λ) (N + 1) t :=
  IsingModel.mayerPartialSum_succ (inducedGraph G Λ) N t

/-- **Λ-layer: mayerExpansionTerm = mayerPartialSum diff**. -/
theorem mayerExpansionTerm_Λ_eq_mayerPartialSum_diff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) (N + 1) t =
      IsingModel.mayerPartialSum (inducedGraph G Λ) (N + 1) t -
        IsingModel.mayerPartialSum (inducedGraph G Λ) N t :=
  IsingModel.mayerExpansionTerm_eq_mayerPartialSum_diff
    (inducedGraph G Λ) N t

/-- **Λ-layer: polymerFreeEnergy hasSum via log under `|ε(t)| < 1`**. -/
theorem polymerFreeEnergy_Λ_hasSum_via_log
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ}
    (h_abs : |∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                        (inducedGraph G Λ)).erase ∅,
                ∏ P ∈ Γ, t ^ P.card| < 1) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                    (inducedGraph G Λ)).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
          (n + 1))
      (IsingModel.polymerFreeEnergy (inducedGraph G Λ) t) :=
  IsingModel.polymerFreeEnergy_hasSum_via_log (inducedGraph G Λ) h_abs

/-- **Λ-layer: polymerFreeEnergy hasSum eventually as `t → 0`**. -/
theorem polymerFreeEnergy_Λ_hasSum_via_log_eventually
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    ∀ᶠ t : ℝ in nhds 0,
      HasSum (fun n : ℕ =>
          (-1 : ℝ) ^ n *
            (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                      (inducedGraph G Λ)).erase ∅,
                ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
            (n + 1))
        (IsingModel.polymerFreeEnergy (inducedGraph G Λ) t) :=
  IsingModel.polymerFreeEnergy_hasSum_via_log_eventually
    (inducedGraph G Λ)

/-- **Λ-layer: ε(t) → 0 as t → 0**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_tendsto_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Filter.Tendsto (fun t : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) (nhds 0) (nhds 0) :=
  IsingModel.vdPolymerFamilies_sum_minus_one_tendsto_zero
    (inducedGraph G Λ)

/-! ### §18.5 ε(t) infrastructure + Mayer term sign + allPolymers
empty Λ-layer wraps -/

/-- **Λ-layer: 0 ≤ mayerExpansionTerm at n = 1** under `0 ≤ t`. -/
theorem mayerExpansionTerm_Λ_one_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ IsingModel.mayerExpansionTerm (inducedGraph G Λ) 1 t :=
  IsingModel.mayerExpansionTerm_one_nonneg_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: mayerExpansionTerm at n = 2 ≤ 0** under `0 ≤ t`. -/
theorem mayerExpansionTerm_Λ_two_nonpos_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) 2 t ≤ 0 :=
  IsingModel.mayerExpansionTerm_two_nonpos_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: ε(0) = 0**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 0 :=
  IsingModel.vdPolymerFamilies_sum_minus_one_at_zero (inducedGraph G Λ)

/-- **Λ-layer: ε(t) is `Continuous`**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_continuous
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Continuous (fun t : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_minus_one_continuous
    (inducedGraph G Λ)

/-- **Λ-layer: ε(t) is `AnalyticAt ℝ` at every `t`**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_analyticAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, s ^ P.card) t :=
  IsingModel.vdPolymerFamilies_sum_minus_one_analyticAt
    (inducedGraph G Λ) t

/-- **Λ-layer: ε(t) < 1 eventually as t → 0**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_lt_one_eventually
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    ∀ᶠ t : ℝ in nhds 0,
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) < 1 :=
  IsingModel.vdPolymerFamilies_sum_minus_one_lt_one_eventually
    (inducedGraph G Λ)

/-- **Λ-layer: allPolymers = ∅ on edgeless induced graphs**. -/
theorem allPolymers_Λ_eq_empty_of_edgeFinset_empty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_empty : (inducedGraph G Λ).edgeFinset = ∅) :
    IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.allPolymers_eq_empty_of_edgeFinset_empty
    (inducedGraph G Λ) h_empty


end Ambient

end IsingModel
