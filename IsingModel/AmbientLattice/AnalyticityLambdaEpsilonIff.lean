import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.StrictPositivity.StrictMono

/-!
# AmbientLattice/Analyticity ε(t) positivity-iff + strict-mono wrappers

Narrow child module for 16 §18.5 Λ-layer wrappers covering:

- ε(t) / polymerFreeEnergy positivity / zero iff family
  (`vdPolymerFamilies_sum_Λ_minus_one_{pos_iff, eq_zero_iff,
  tanh_pos_iff, tanh_eq_zero_iff}`,
  `polymerFreeEnergy_Λ_tanh_{pos_iff, eq_zero_iff}`).
- strict-mono / strict-pos under polymers ≠ ∅
  (`vdPolymerFamilies_sum_Λ_lt_of_lt_of_polymers_nonempty`,
  `vdPolymerFamilies_sum_Λ_strictMonoOn_of_polymers_nonempty`,
  `polymerFreeEnergy_Λ_pos_of_t_pos_of_polymers_nonempty`,
  `vdPolymerFamilies_sum_Λ_gt_one_of_t_pos_of_polymers_nonempty`,
  `vdPolymerFamilies_sum_Λ_minus_one_pos_of_t_pos_of_polymers_nonempty`,
  `polymerFreeEnergy_Λ_tanh_pos_of_tanh_pos_of_polymers_nonempty`,
  `vdPolymerFamilies_sum_Λ_tanh_gt_one_of_tanh_pos_of_polymers_nonempty`,
  `vdPolymerFamilies_sum_Λ_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty`,
  `polymerFreeEnergy_Λ_strictMonoOn_Ioi_zero_of_polymers_nonempty`,
  `vdPolymerFamilies_sum_Λ_strictMonoOn_Ioi_zero_of_polymers_nonempty`).

The theorem names are unchanged from the former `Analyticity`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 ε(t) / polymerFreeEnergy positivity-iff Λ-layer wraps -/

/-- **Λ-layer: 0 < ε(t) ↔ 0 < t ∧ allPolymers ≠ ∅** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_pos_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ↔
      0 < t ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.vdPolymerFamilies_sum_minus_one_pos_iff
    (inducedGraph G Λ) ht

/-- **Λ-layer: ε(t) = 0 ↔ t = 0 ∨ allPolymers = ∅** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_eq_zero_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 ↔
      t = 0 ∨ IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.vdPolymerFamilies_sum_minus_one_eq_zero_iff
    (inducedGraph G Λ) ht

/-- **Λ-layer: 0 < ε(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅** under
`0 ≤ β·J`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_tanh_pos_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.vdPolymerFamilies_sum_minus_one_tanh_pos_iff
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: ε(tanh) = 0 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_tanh_eq_zero_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.vdPolymerFamilies_sum_minus_one_tanh_eq_zero_iff
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: 0 < polymerFreeEnergy(tanh) ↔ 0 < tanh ∧
allPolymers ≠ ∅** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_pos_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.polymerFreeEnergy_tanh_pos_iff (inducedGraph G Λ) hβJ

/-- **Λ-layer: polymerFreeEnergy(tanh) = 0 ↔ tanh = 0 ∨
allPolymers = ∅** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_eq_zero_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.polymerFreeEnergy_tanh_eq_zero_iff
    (inducedGraph G Λ) hβJ

/-! ### §18.5 strict-mono / strict-pos under polymers ≠ ∅
Λ-layer wraps -/

/-- **Λ-layer: vdSum(s) < vdSum(t) for `0 ≤ s < t`** under polymers
exist. -/
theorem vdPolymerFamilies_sum_Λ_lt_of_lt_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, s ^ P.card) <
      ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_lt_of_lt_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hs hst

/-- **Λ-layer: vdSum is `StrictMonoOn (Set.Ici 0)`** under polymers
exist. -/
theorem vdPolymerFamilies_sum_Λ_strictMonoOn_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  IsingModel.vdPolymerFamilies_sum_strictMonoOn_of_polymers_nonempty
    (inducedGraph G Λ) h_poly

/-- **Λ-layer: 0 < pFE under `0 < t` and polymers exist**. -/
theorem polymerFreeEnergy_Λ_pos_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ) t :=
  IsingModel.polymerFreeEnergy_pos_of_t_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_t_pos h_poly

/-- **Λ-layer: 1 < vdSum under `0 < t` and polymers exist**. -/
theorem vdPolymerFamilies_sum_Λ_gt_one_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
            ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_gt_one_of_t_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_t_pos h_poly

/-- **Λ-layer: 0 < ε(t) under `0 < t` and polymers exist**. -/
theorem
vdPolymerFamilies_sum_Λ_minus_one_pos_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_minus_one_pos_of_t_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_t_pos h_poly

/-- **Λ-layer: 0 < pFE(tanh) under `0 < tanh` and polymers exist**. -/
theorem polymerFreeEnergy_Λ_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J))
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) :=
  IsingModel.polymerFreeEnergy_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_tanh_pos h_poly

/-- **Λ-layer: 1 < vdSum(tanh) under `0 < tanh` and polymers exist**. -/
theorem
vdPolymerFamilies_sum_Λ_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J))
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_tanh_pos h_poly

/-- **Λ-layer: 0 < ε(tanh) under `0 < tanh` and polymers exist**. -/
theorem
vdPolymerFamilies_sum_Λ_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J))
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_tanh_pos h_poly

/-- **Λ-layer: pFE is `StrictMonoOn (Set.Ioi 0)`** under polymers
exist. -/
theorem polymerFreeEnergy_Λ_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    StrictMonoOn (fun t : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G Λ) t) (Set.Ioi 0) :=
  IsingModel.polymerFreeEnergy_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (inducedGraph G Λ) h_poly

/-- **Λ-layer: vdSum is `StrictMonoOn (Set.Ioi 0)`** under polymers
exist. -/
theorem
vdPolymerFamilies_sum_Λ_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ioi 0) :=
  IsingModel.vdPolymerFamilies_sum_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (inducedGraph G Λ) h_poly


end Ambient

end IsingModel
