import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.StrictPositivity.TanhMonotone

/-!
# AmbientLattice/Analyticity polymerFreeEnergy sharpening + vdSum sandwich wrappers

Narrow child module for 21 §18.5 Λ-layer wrappers covering:

- polymerFreeEnergy tanh sharpening (non-ferromagnetic) + β/J strict-mono
  (`polymerFreeEnergy_Λ_tanh_{lt_eps_iff_eps_pos,
  eq_zero_iff_eps_eq_zero, pos_iff_eps_pos, lt_eps_of_eps_pos,
  lt_pow_sub_one_of_eps_pos}` under `0 ≤ β·J`;
  `_tanh_{lt_of_lt_in_beta, lt_of_lt_in_J, strictMonoOn_beta,
  strictMonoOn_J}_of_polymers_nonempty`).
- ε(t) nonneg + non-tanh polymerFreeEnergy sharpening
  (`vdPolymerFamilies_sum_Λ_minus_one_{nonneg_of_nonneg, pow_at_zero}`,
  `polymerFreeEnergy_Λ_{eq_zero_iff_eps_eq_zero, pos_iff_eps_pos,
  lt_eps_iff_eps_pos, lt_pow_sub_one_of_eps_pos}`).
- vdSum sandwich/monotone + ε bound + pFE(tanh) bound + log2
  (`vdPolymerFamilies_sum_Λ_{sandwich_of_nonneg, monotoneOn_Ici_zero,
  minus_one_le_of_nonneg}`,
  `polymerFreeEnergy_Λ_tanh_{le_eps_of_betaJ_nonneg,
  le_pow_sub_one_of_betaJ_nonneg, lt_log_two_of_pow_lt_two}`).

The theorem names are unchanged from the former `Analyticity`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 polymerFreeEnergy tanh sharpening + β/J strict-mono
Λ-layer wraps -/

/-- **Λ-layer: pFE(tanh) < ε(tanh) ↔ 0 < ε(tanh)** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_lt_eps_iff_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
              ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_lt_eps_iff_eps_pos
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: pFE(tanh) = 0 ↔ ε(tanh) = 0** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_eq_zero_iff_eps_eq_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  IsingModel.polymerFreeEnergy_tanh_eq_zero_iff_eps_eq_zero
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: 0 < pFE(tanh) ↔ 0 < ε(tanh)** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_pos_iff_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_pos_iff_eps_pos
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: pFE(tanh) < ε(tanh)** under ε(tanh) > 0 (`0 ≤ β·J`). -/
theorem polymerFreeEnergy_Λ_tanh_lt_eps_of_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_lt_eps_of_eps_pos
    (inducedGraph G Λ) hβJ h_eps_pos

/-- **Λ-layer: pFE(tanh) < (1+tanh)^|E| - 1** under ε(tanh) > 0
(`0 ≤ β·J`). -/
theorem polymerFreeEnergy_Λ_tanh_lt_pow_sub_one_of_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.polymerFreeEnergy_tanh_lt_pow_sub_one_of_eps_pos
    (inducedGraph G Λ) hβJ h_eps_pos

/-- **Λ-layer: pFE(tanh(β₁·J)) < pFE(tanh(β₂·J))** under `J > 0`,
`0 ≤ β₁ < β₂`, polymers nonempty. -/
theorem polymerFreeEnergy_Λ_tanh_lt_of_lt_in_beta_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {β₁ β₂ J : ℝ} (hβ₁ : 0 ≤ β₁) (hJ : 0 < J) (hβ : β₁ < β₂) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β₁ * J)) <
      IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β₂ * J)) :=
  IsingModel.polymerFreeEnergy_tanh_lt_of_lt_in_beta_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hβ₁ hJ hβ

/-- **Λ-layer: pFE(tanh(β·J₁)) < pFE(tanh(β·J₂))** under `β > 0`,
`0 ≤ J₁ < J₂`, polymers nonempty. -/
theorem polymerFreeEnergy_Λ_tanh_lt_of_lt_in_J_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {β J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hβ : 0 < β) (hJ : J₁ < J₂) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J₁)) <
      IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J₂)) :=
  IsingModel.polymerFreeEnergy_tanh_lt_of_lt_in_J_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hJ₁ hβ hJ

/-- **Λ-layer: pFE(tanh(β·J)) is `StrictMonoOn (Set.Ici 0)` in β**
under `J > 0` and polymers nonempty. -/
theorem
polymerFreeEnergy_Λ_tanh_strictMonoOn_beta_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {J : ℝ} (hJ : 0 < J) :
    StrictMonoOn (fun β : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G Λ) (Real.tanh (β * J))) (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_tanh_strictMonoOn_beta_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hJ

/-- **Λ-layer: pFE(tanh(β·J)) is `StrictMonoOn (Set.Ici 0)` in J**
under `β > 0` and polymers nonempty. -/
theorem polymerFreeEnergy_Λ_tanh_strictMonoOn_J_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {β : ℝ} (hβ : 0 < β) :
    StrictMonoOn (fun J : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G Λ) (Real.tanh (β * J))) (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_tanh_strictMonoOn_J_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hβ

/-! ### §18.5 ε(t) nonneg + non-tanh polymerFreeEnergy sharpening
Λ-layer wraps -/

/-- **Λ-layer: 0 ≤ ε(t)** for `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_minus_one_nonneg_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: ε(0)^n = 0** for `n ≥ 1`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_pow_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {n : ℕ} (hn : 1 ≤ n) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, (0 : ℝ) ^ P.card) ^ n = 0 :=
  IsingModel.vdPolymerFamilies_sum_minus_one_pow_at_zero
    (inducedGraph G Λ) hn

/-- **Λ-layer: pFE(t) = 0 ↔ ε(t) = 0** under `0 ≤ t`. -/
theorem polymerFreeEnergy_Λ_eq_zero_iff_eps_eq_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 :=
  IsingModel.polymerFreeEnergy_eq_zero_iff_eps_eq_zero
    (inducedGraph G Λ) ht

/-- **Λ-layer: 0 < pFE(t) ↔ 0 < ε(t)** under `0 ≤ t`. -/
theorem polymerFreeEnergy_Λ_pos_iff_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.polymerFreeEnergy_pos_iff_eps_pos (inducedGraph G Λ) ht

/-- **Λ-layer: pFE(t) < ε(t) ↔ 0 < ε(t)** under `0 ≤ t`. -/
theorem polymerFreeEnergy_Λ_lt_eps_iff_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.polymerFreeEnergy_lt_eps_iff_eps_pos
    (inducedGraph G Λ) ht

/-- **Λ-layer: pFE(t) < (1+t)^|E| - 1** under `0 ≤ t` and ε(t) > 0. -/
theorem polymerFreeEnergy_Λ_lt_pow_sub_one_of_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t <
      (1 + t) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.polymerFreeEnergy_lt_pow_sub_one_of_eps_pos
    (inducedGraph G Λ) ht h_eps_pos

/-! ### §18.5 vdSum sandwich/monotone + ε bound + pFE(tanh) bound +
log2 Λ-layer wraps -/

/-- **Λ-layer: vdSum sandwich for `t ≥ 0`**: `1 ≤ vdSum ≤
(1+t)^|E|`. -/
theorem vdPolymerFamilies_sum_Λ_sandwich_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_sandwich_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: vdSum is `MonotoneOn (Set.Ici 0)`**. -/
theorem vdPolymerFamilies_sum_Λ_monotoneOn_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    MonotoneOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  IsingModel.vdPolymerFamilies_sum_monotoneOn_Ici_zero (inducedGraph G Λ)

/-- **Λ-layer: ε(t) ≤ (1+t)^|E| - 1** for `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_le_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.vdPolymerFamilies_sum_minus_one_le_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: pFE(tanh) ≤ ε(tanh) under `0 ≤ β·J`**. -/
theorem polymerFreeEnergy_Λ_tanh_le_eps_of_betaJ_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_le_eps_of_betaJ_nonneg
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: pFE(tanh) ≤ (1+tanh)^|E| - 1 under `0 ≤ β·J`**. -/
theorem polymerFreeEnergy_Λ_tanh_le_pow_sub_one_of_betaJ_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (1 + Real.tanh (β * J)) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.polymerFreeEnergy_tanh_le_pow_sub_one_of_betaJ_nonneg
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: pFE(tanh) < log 2** under `(1+tanh)^|E| < 2` and
`0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_lt_log_two_of_pow_lt_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) < Real.log 2 :=
  IsingModel.polymerFreeEnergy_tanh_lt_log_two_of_pow_lt_two
    (inducedGraph G Λ) hβJ h_pow


end Ambient

end IsingModel
