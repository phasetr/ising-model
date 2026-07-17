import IsingModel.ClusterExpansion.MayerCore.LogTaylor

/-!
# High-temperature polymer bounds

Mechanical child split from `ClusterExpansion.HighTempGeneralRegularity`.
-/

namespace IsingModel

open Finset
/-- **`polymerFreeEnergy ≤ ε(t)` under `0 ≤ t`** (§18.4 sharpening):
the polymer free energy is bounded above by the polymer-family
activity excess `ε(t) = ∑_{Γ ≠ ∅} ∏ t^|P|`. Proof: from `Real.log(1+x) ≤ x`
for `x ≥ -1` (via `Real.add_one_le_exp`) applied to `x = ε(t) ≥ 0`. -/
theorem polymerFreeEnergy_le_eps_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    polymerFreeEnergy G t ≤
      ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card := by
  rw [polymerFreeEnergy_eq_log_one_add_eps]
  set ε := ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
    ∏ P ∈ Γ, t ^ P.card
  have hε : 0 ≤ ε := vdPolymerFamilies_sum_minus_one_nonneg_of_nonneg G ht
  have h_pos : 0 < 1 + ε := by linarith
  have h_le : 1 + ε ≤ Real.exp ε := by
    have := Real.add_one_le_exp ε
    linarith
  exact (Real.log_le_iff_le_exp h_pos).mpr h_le

/-- **`polymerFreeEnergy = 0 ↔ ε(t) = 0` under `0 ≤ t`** (§18.4
sharpening): the polymer free energy vanishes iff the polymer-family
activity excess vanishes. Proof: `polymerFreeEnergy = log(1+ε)`,
and for `ε ≥ 0`, log(1+ε) = 0 iff 1+ε = 1 iff ε = 0. -/
theorem polymerFreeEnergy_eq_zero_iff_eps_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    polymerFreeEnergy G t = 0 ↔
      (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) = 0 := by
  rw [polymerFreeEnergy_eq_log_one_add_eps]
  set ε := ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
    ∏ P ∈ Γ, t ^ P.card
  have hε : 0 ≤ ε := vdPolymerFamilies_sum_minus_one_nonneg_of_nonneg G ht
  have h_pos : 0 < 1 + ε := by linarith
  rw [Real.log_eq_zero]
  refine ⟨?_, ?_⟩
  · rintro (h | h | h)
    · linarith
    · linarith
    · linarith
  · intro hε_zero
    right; left; linarith

/-- **`0 < polymerFreeEnergy ↔ 0 < ε(t)` under `0 ≤ t`** (§18.4
sharpening): the polymer free energy is strictly positive iff the
polymer-family activity excess is strictly positive. Direct corollary
of `polymerFreeEnergy_eq_zero_iff_eps_eq_zero` combined with
`polymerFreeEnergy_nonneg_of_nonneg` and
`vdPolymerFamilies_sum_minus_one_nonneg_of_nonneg`. -/
theorem polymerFreeEnergy_pos_iff_eps_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < polymerFreeEnergy G t ↔
      0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card := by
  have h_pf_nn := polymerFreeEnergy_nonneg_of_nonneg G ht
  have h_eps_nn := vdPolymerFamilies_sum_minus_one_nonneg_of_nonneg G ht
  have h_eq := polymerFreeEnergy_eq_zero_iff_eps_eq_zero G ht
  constructor
  · intro h_pf_pos
    by_contra h_eps_not_pos
    push Not at h_eps_not_pos
    have h_eps_zero : (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) = 0 := le_antisymm h_eps_not_pos h_eps_nn
    rw [← h_eq] at h_eps_zero
    linarith
  · intro h_eps_pos
    by_contra h_pf_not_pos
    push Not at h_pf_not_pos
    have h_pf_zero : polymerFreeEnergy G t = 0 := le_antisymm h_pf_not_pos h_pf_nn
    rw [h_eq] at h_pf_zero
    linarith

/-- **`polymerFreeEnergy < ε(t)` when `ε(t) > 0`** (§18.4 strict
sharpening): when the polymer-family activity excess is strictly
positive, the polymer free energy is *strictly* less than `ε(t)`.
Proof: `Real.log_lt_sub_one_of_pos` gives `log(1+ε) < (1+ε) - 1 = ε`
for `1 + ε > 0` and `1 + ε ≠ 1`, i.e., `ε > 0`. Strengthens
`polymerFreeEnergy_le_eps_of_nonneg` to strict inequality in the
non-degenerate regime. -/
theorem polymerFreeEnergy_lt_eps_of_eps_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (h_eps_pos : 0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, t ^ P.card) :
    polymerFreeEnergy G t <
      ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card := by
  rw [polymerFreeEnergy_eq_log_one_add_eps]
  set ε := ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
    ∏ P ∈ Γ, t ^ P.card with hε_def
  have h_pos : 0 < 1 + ε := by linarith
  have h_ne_one : 1 + ε ≠ 1 := by linarith
  have h := Real.log_lt_sub_one_of_pos h_pos h_ne_one
  linarith

/-- **`polymerFreeEnergy < ε(t) ↔ ε(t) > 0` under `0 ≤ t`** (§18.4
strict iff): the polymer free energy is strictly below the activity
excess iff the activity excess is strictly positive. Forward: from
the contrapositive ε ≤ 0 → ε = 0 → polymerFreeEnergy = 0 = ε.
Backward: from `polymerFreeEnergy_lt_eps_of_eps_pos` (PR #1547). -/
theorem polymerFreeEnergy_lt_eps_iff_eps_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    polymerFreeEnergy G t <
        ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
          ∏ P ∈ Γ, t ^ P.card ↔
      0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card := by
  have h_eps_nn := vdPolymerFamilies_sum_minus_one_nonneg_of_nonneg G ht
  refine ⟨?_, fun h => polymerFreeEnergy_lt_eps_of_eps_pos G h⟩
  intro h_lt
  by_contra h_eps_not_pos
  push Not at h_eps_not_pos
  have h_eps_zero :
      (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) = 0 := le_antisymm h_eps_not_pos h_eps_nn
  have h_pf_zero := (polymerFreeEnergy_eq_zero_iff_eps_eq_zero G ht).mpr h_eps_zero
  rw [h_pf_zero, h_eps_zero] at h_lt
  exact lt_irrefl 0 h_lt

/-- **`polymerFreeEnergy ≤ (1+t)^|E| - 1` under `0 ≤ t`** (§18.4
sharpening): combines `polymerFreeEnergy ≤ ε(t)` (above) with Step 661
(`ε(t) ≤ (1+t)^|E| - 1`). Sharper than the existing
`polymerFreeEnergy ≤ |E|·log(1+t)` (Step 630) for moderate `t`,
since `(1+t)^|E| - 1` grows polynomially while `|E|·log(1+t)`
grows logarithmically — but the new bound is meaningful in the
regime `(1+t)^|E| < 2` where the cluster expansion converges. -/
theorem polymerFreeEnergy_le_pow_sub_one_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    polymerFreeEnergy G t ≤ (1 + t) ^ G.edgeFinset.card - 1 :=
  (polymerFreeEnergy_le_eps_of_nonneg G ht).trans
    (vdPolymerFamilies_sum_minus_one_le_of_nonneg G ht)

/-- **`polymerFreeEnergy < (1+t)^|E| - 1` when `ε(t) > 0` and `0 ≤ t`**
(§18.4 strict sharpening): combines `polymerFreeEnergy_lt_eps_of_eps_pos`
(PR #1547) with `vdPolymerFamilies_sum_minus_one_le_of_nonneg` (Step 661).
The `<` is from the first; the `≤` from the second is composed.
Strengthens `polymerFreeEnergy_le_pow_sub_one_of_nonneg` (above) to
strict inequality in the non-degenerate regime. -/
theorem polymerFreeEnergy_lt_pow_sub_one_of_eps_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (h_eps_pos : 0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, t ^ P.card) :
    polymerFreeEnergy G t < (1 + t) ^ G.edgeFinset.card - 1 :=
  (polymerFreeEnergy_lt_eps_of_eps_pos G h_eps_pos).trans_le
    (vdPolymerFamilies_sum_minus_one_le_of_nonneg G ht)

/-- **Tanh form of `polymerFreeEnergy < (1+t)^|E| - 1`** under `0 ≤ β·J`
and tanh-substituted ε > 0 (§18.4 sharpening, ferromagnetic). -/
theorem polymerFreeEnergy_tanh_lt_pow_sub_one_of_eps_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_eps_pos : 0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    polymerFreeEnergy G (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^ G.edgeFinset.card - 1 :=
  polymerFreeEnergy_lt_pow_sub_one_of_eps_pos G (real_tanh_nonneg hβJ) h_eps_pos

/-- **`polymerFreeEnergy < log 2` under `(1+t)^|E| < 2` and `0 ≤ t`**
(§18.4 high-temperature sharpening): in the cluster-expansion
convergence regime (where `polymerFreeEnergy_hasSum_via_log_of_pow_lt_two`
applies), `polymerFreeEnergy G t < Real.log 2`.

Proof: `polymerFreeEnergy G t = log(1 + ε(t))` with
`ε(t) ≤ (1+t)^|E| - 1 < 1` (Step 661 + hypothesis), hence
`1 + ε(t) < 2` and `log` strict-monotone gives `log(1+ε) < log 2`. -/
theorem polymerFreeEnergy_lt_log_two_of_pow_lt_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (h_pow : (1 + t) ^ G.edgeFinset.card < 2) :
    polymerFreeEnergy G t < Real.log 2 := by
  rw [polymerFreeEnergy_eq_log_one_add_eps]
  set ε := ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
    ∏ P ∈ Γ, t ^ P.card
  have hε : 0 ≤ ε := vdPolymerFamilies_sum_minus_one_nonneg_of_nonneg G ht
  have hε_le : ε ≤ (1 + t) ^ G.edgeFinset.card - 1 :=
    vdPolymerFamilies_sum_minus_one_le_of_nonneg G ht
  have h_lt_one : ε < 1 := by linarith
  have h_pos : 0 < 1 + ε := by linarith
  have h_lt_two : 1 + ε < 2 := by linarith
  exact (Real.log_lt_log_iff h_pos (by norm_num : (0 : ℝ) < 2)).mpr h_lt_two

/-- **`polymerFreeEnergy ≤ ε(tanh(β·J))` under `0 ≤ β·J`** (§18.4
sharpening, tanh form): the ferromagnetic-Ising specialisation of
`polymerFreeEnergy_le_eps_of_nonneg`. Substituting `t = tanh(β·J)`
(non-negative under `0 ≤ β·J`), the polymer free energy is bounded
above by the polymer-family activity excess at activity `tanh(β·J)`. -/
theorem polymerFreeEnergy_tanh_le_eps_of_betaJ_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_le_eps_of_nonneg G (real_tanh_nonneg hβJ)

/-- **`polymerFreeEnergy ≤ (1+tanh(β·J))^|E| - 1` under `0 ≤ β·J`**
(§18.4 sharpening, tanh form): tanh-substituted form of
`polymerFreeEnergy_le_pow_sub_one_of_nonneg`. -/
theorem polymerFreeEnergy_tanh_le_pow_sub_one_of_betaJ_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      (1 + Real.tanh (β * J)) ^ G.edgeFinset.card - 1 :=
  polymerFreeEnergy_le_pow_sub_one_of_nonneg G (real_tanh_nonneg hβJ)

/-- **`polymerFreeEnergy < log 2` under `(1+tanh(β·J))^|E| < 2` and
`0 ≤ β·J`** (§18.4 sharpening, tanh form): tanh-substituted form of
`polymerFreeEnergy_lt_log_two_of_pow_lt_two`. -/
theorem polymerFreeEnergy_tanh_lt_log_two_of_pow_lt_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_pow : (1 + Real.tanh (β * J)) ^ G.edgeFinset.card < 2) :
    polymerFreeEnergy G (Real.tanh (β * J)) < Real.log 2 :=
  polymerFreeEnergy_lt_log_two_of_pow_lt_two G (real_tanh_nonneg hβJ) h_pow

/-- **`polymerFreeEnergy` high-temperature regime sandwich**
(§18.4 sharpening): under `0 ≤ t` and `(1+t)^|E| < 2`,
  `0 ≤ polymerFreeEnergy G t ≤ ε(t) ≤ (1+t)^|E| - 1 < 1`,
hence in particular `polymerFreeEnergy G t < log 2`.

Single-statement bundle of the high-temperature convergence-regime
bounds — combines `polymerFreeEnergy_nonneg_of_nonneg`,
`polymerFreeEnergy_le_eps_of_nonneg`,
`vdPolymerFamilies_sum_minus_one_le_of_nonneg` (Step 661), and the
hypothesis `(1+t)^|E| < 2`. -/
theorem polymerFreeEnergy_high_temp_sandwich
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (h_pow : (1 + t) ^ G.edgeFinset.card < 2) :
    0 ≤ polymerFreeEnergy G t ∧
    polymerFreeEnergy G t ≤
      ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card ∧
    (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) ≤ (1 + t) ^ G.edgeFinset.card - 1 ∧
    (1 + t) ^ G.edgeFinset.card - 1 < 1 ∧
    polymerFreeEnergy G t < Real.log 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact polymerFreeEnergy_nonneg_of_nonneg G ht
  · exact polymerFreeEnergy_le_eps_of_nonneg G ht
  · exact vdPolymerFamilies_sum_minus_one_le_of_nonneg G ht
  · linarith
  · exact polymerFreeEnergy_lt_log_two_of_pow_lt_two G ht h_pow

/-- **`polymerFreeEnergy` high-temperature regime sandwich (tanh form)**
(§18.4 sharpening): tanh-substituted version of
`polymerFreeEnergy_high_temp_sandwich` for the ferromagnetic Ising
activity `t = tanh(β·J)` under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_tanh_high_temp_sandwich
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_pow : (1 + Real.tanh (β * J)) ^ G.edgeFinset.card < 2) :
    0 ≤ polymerFreeEnergy G (Real.tanh (β * J)) ∧
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ∧
    (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ≤
      (1 + Real.tanh (β * J)) ^ G.edgeFinset.card - 1 ∧
    (1 + Real.tanh (β * J)) ^ G.edgeFinset.card - 1 < 1 ∧
    polymerFreeEnergy G (Real.tanh (β * J)) < Real.log 2 :=
  polymerFreeEnergy_high_temp_sandwich G (real_tanh_nonneg hβJ) h_pow

/-- **`polymerFreeEnergy` high-temperature regime sandwich
(ferromagnetic tanh form)** (§18.5 ferromagnetic): under
`0 ≤ J, 0 < β`, the same 5-statement sandwich. -/
theorem polymerFreeEnergy_tanh_high_temp_sandwich_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (h_pow : (1 + Real.tanh (β * J)) ^ G.edgeFinset.card < 2) :
    0 ≤ polymerFreeEnergy G (Real.tanh (β * J)) ∧
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ∧
    (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ≤
      (1 + Real.tanh (β * J)) ^ G.edgeFinset.card - 1 ∧
    (1 + Real.tanh (β * J)) ^ G.edgeFinset.card - 1 < 1 ∧
    polymerFreeEnergy G (Real.tanh (β * J)) < Real.log 2 :=
  polymerFreeEnergy_tanh_high_temp_sandwich G
    (mul_nonneg hβ.le hJ) h_pow

/-- **`freeEnergy` strict upper bound in cluster-expansion convergence
regime** (§18.4 capstone): under `0 ≤ β·J`, `0 < |ι|`, and
`(1+tanh(β·J))^|E| < 2`,
  freeEnergy G ⟨J, 0, β⟩ < log 2 + (|E|/|ι|) · log cosh(β·J) + log 2 / |ι|.

Combines `freeEnergy_eq_polymerFreeEnergy` (Step 612) with the
strict bound `polymerFreeEnergy < log 2` from PR #1524. -/
theorem freeEnergy_lt_log_two_plus_high_temp_correction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι)
    (h_pow : (1 + Real.tanh (β * J)) ^ G.edgeFinset.card < 2) :
    freeEnergy G ⟨J, 0, β⟩ <
      Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J)) +
        Real.log 2 / Fintype.card ι := by
  rw [freeEnergy_eq_polymerFreeEnergy G J β hβJ hne]
  have h_lt : polymerFreeEnergy G (Real.tanh (β * J)) < Real.log 2 :=
    polymerFreeEnergy_lt_log_two_of_pow_lt_two G (real_tanh_nonneg hβJ) h_pow
  have h_pos : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hne
  have h_div_lt : polymerFreeEnergy G (Real.tanh (β * J)) / (Fintype.card ι : ℝ) <
      Real.log 2 / (Fintype.card ι : ℝ) :=
    div_lt_div_of_pos_right h_lt h_pos
  linarith

/-- **Ferromagnetic strict `freeEnergy` upper bound in cluster-expansion
convergence regime** (§18.5): under `0 ≤ J, 0 < β`, `0 < |ι|`, and
`(1+tanh(β·J))^|E| < 2`, the same strict upper bound. -/
theorem freeEnergy_lt_log_two_plus_high_temp_correction_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι)
    (h_pow : (1 + Real.tanh (β * J)) ^ G.edgeFinset.card < 2) :
    freeEnergy G ⟨J, 0, β⟩ <
      Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J)) +
        Real.log 2 / Fintype.card ι :=
  freeEnergy_lt_log_two_plus_high_temp_correction
    G J β (mul_nonneg hβ.le hJ) hne h_pow

end IsingModel
