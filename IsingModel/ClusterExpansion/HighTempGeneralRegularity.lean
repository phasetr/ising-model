import IsingModel.ClusterExpansion.AlternatingCompleteGraph

/-!
# Cluster expansion high-temperature bounds and general regularity

Mechanical child split from `ClusterExpansion.lean`.
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

/-- **Partition function `AnalyticAt ℝ` in `β` at general `h`** (§18.6
extension): for any `(J, h, β)`, `Z(β) = ∑_σ exp(-β · H(σ))` is real-
analytic in `β`. Direct proof: each summand `exp(-β · H(σ))` is
`exp ∘ (linear in β)`, which is analytic; sum of analytic functions
over a finite finset is analytic. Extends `partitionFunction_analyticAt_beta_h_zero`
(Step 563) from `h = 0` to arbitrary `h`. -/
theorem partitionFunction_analyticAt_beta_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => partitionFunction G ⟨J, h, β'⟩) β := by
  have h_eq : (fun β' : ℝ => partitionFunction G ⟨J, h, β'⟩) =
      fun β' : ℝ => ∑ σ : Config ι,
        Real.exp ((-hamiltonian G ⟨J, h, β⟩ σ) * β') := by
    funext β'
    unfold partitionFunction boltzmannWeight
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    have h_ham : hamiltonian G ⟨J, h, β'⟩ σ = hamiltonian G ⟨J, h, β⟩ σ := rfl
    rw [h_ham]; ring_nf
  rw [h_eq]
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  exact analyticAt_rexp.comp (analyticAt_const.mul analyticAt_id)

/-- **Free energy `AnalyticAt ℝ` in `β` at general `h`** (§18.6
extension): `f = (1/|ι|) · log Z` is real-analytic in `β` at every
point, for any `J, h`. Composes `partitionFunction_analyticAt_beta_general_h`
with `AnalyticAt.log` (using `partitionFunction_pos`). -/
theorem freeEnergy_analyticAt_beta_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => freeEnergy G ⟨J, h, β'⟩) β := by
  unfold freeEnergy
  refine analyticAt_const.mul ?_
  exact (partitionFunction_analyticAt_beta_general_h G J h β).log
    (partitionFunction_pos G _)

/-- **Partition function `AnalyticAt ℝ` in `J` at general `h`** (§18.6
extension): for any `(β, h, J)`, `Z(J) = ∑_σ exp(-β · H(σ))` is real-
analytic in `J`, since the Hamiltonian depends linearly on `J` (only
through the interaction term). Direct proof analogous to
`partitionFunction_analyticAt_beta_general_h`. -/
theorem partitionFunction_analyticAt_J_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β h J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => partitionFunction G ⟨J', h, β⟩) J := by
  have h_eq : (fun J' : ℝ => partitionFunction G ⟨J', h, β⟩) =
      fun J' : ℝ => ∑ σ : Config ι,
        Real.exp ((β * (∑ e ∈ G.edgeFinset, edgeSpin σ e)) * J' +
          (-β * externalFieldEnergy h σ)) := by
    funext J'
    unfold partitionFunction boltzmannWeight hamiltonian interactionEnergy
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    congr 1
    ring_nf
  rw [h_eq]
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine analyticAt_rexp.comp ?_
  exact (analyticAt_const.mul analyticAt_id).add analyticAt_const

/-- **Free energy `AnalyticAt ℝ` in `J` at general `h`** (§18.6
extension): `f = (1/|ι|) · log Z` is real-analytic in `J` at every
point, for any `β, h`. Composes `partitionFunction_analyticAt_J_general_h`
with `AnalyticAt.log` (using `partitionFunction_pos`). -/
theorem freeEnergy_analyticAt_J_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β h J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => freeEnergy G ⟨J', h, β⟩) J := by
  unfold freeEnergy
  refine analyticAt_const.mul ?_
  exact (partitionFunction_analyticAt_J_general_h G β h J).log
    (partitionFunction_pos G _)

/-- **Free energy `AnalyticOnNhd ℝ` in `J` at general `h`** (§18.6
extension): global form of `freeEnergy_analyticAt_J_general_h`. -/
theorem freeEnergy_analyticOnNhd_J_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β h : ℝ) :
    AnalyticOnNhd ℝ (fun J' : ℝ => freeEnergy G ⟨J', h, β⟩) Set.univ :=
  fun J _ => freeEnergy_analyticAt_J_general_h G β h J

/-- **Free energy `AnalyticOnNhd ℝ` in `β` at general `h`** (§18.6
extension): global form of `freeEnergy_analyticAt_beta_general_h`. -/
theorem freeEnergy_analyticOnNhd_beta_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) :
    AnalyticOnNhd ℝ (fun β' : ℝ => freeEnergy G ⟨J, h, β'⟩) Set.univ :=
  fun β _ => freeEnergy_analyticAt_beta_general_h G J h β

/-- **Partition function `AnalyticAt ℝ` in `h`** (§18.6 extension):
for any `(J, β, h)`, `Z(h) = ∑_σ exp(-β · H(σ))` is real-analytic in
`h`. The Hamiltonian is linear in `h` via
`externalFieldEnergy h σ = -h · ∑_i Spin.sign(σ_i)`. Direct proof
analogous to PRs #1528, #1529. -/
theorem partitionFunction_analyticAt_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β h : ℝ) :
    AnalyticAt ℝ (fun h' : ℝ => partitionFunction G ⟨J, h', β⟩) h := by
  have h_eq : (fun h' : ℝ => partitionFunction G ⟨J, h', β⟩) =
      fun h' : ℝ => ∑ σ : Config ι,
        Real.exp ((β * (∑ i : ι, Spin.sign ℝ (σ i))) * h' +
          (-β * interactionEnergy G J σ)) := by
    funext h'
    unfold partitionFunction boltzmannWeight hamiltonian externalFieldEnergy
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    congr 1
    ring_nf
  rw [h_eq]
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine analyticAt_rexp.comp ?_
  exact (analyticAt_const.mul analyticAt_id).add analyticAt_const

/-- **Free energy `AnalyticAt ℝ` in `h`** (§18.6 extension):
`f = (1/|ι|) · log Z` is real-analytic in `h` at every point, for
any `J, β`. -/
theorem freeEnergy_analyticAt_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β h : ℝ) :
    AnalyticAt ℝ (fun h' : ℝ => freeEnergy G ⟨J, h', β⟩) h := by
  unfold freeEnergy
  refine analyticAt_const.mul ?_
  exact (partitionFunction_analyticAt_h G J β h).log
    (partitionFunction_pos G _)

/-- **Free energy `AnalyticOnNhd ℝ` in `h`** (§18.6 extension): global
form of `freeEnergy_analyticAt_h`. -/
theorem freeEnergy_analyticOnNhd_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) :
    AnalyticOnNhd ℝ (fun h' : ℝ => freeEnergy G ⟨J, h', β⟩) Set.univ :=
  fun h _ => freeEnergy_analyticAt_h G J β h

/-- **Partition function jointly `AnalyticAt ℝ` in `(β, J, h)`** (§18.6
extension): for any `(β, J, h)`, `Z(β, J, h) = ∑_σ exp(-β · H(σ))` is
real-analytic JOINTLY in all three Ising parameters at every point.

Proof: each summand `exp(β·J·A_σ + β·h·B_σ)` is `exp ∘ polynomial in
(β, J, h)`, which is analytic jointly via `analyticAt_rexp` composed
with the polynomial; sum over `σ` preserves analyticity. -/
theorem partitionFunction_analyticAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => partitionFunction G ⟨p.2.1, p.2.2, p.1⟩)
      (β, J, h) := by
  -- p = (β', J', h')
  have h_eq : (fun p : ℝ × ℝ × ℝ =>
      partitionFunction G ⟨p.2.1, p.2.2, p.1⟩) =
      fun p : ℝ × ℝ × ℝ => ∑ σ : Config ι,
        Real.exp (p.1 * p.2.1 * (∑ e ∈ G.edgeFinset, edgeSpin σ e) +
          p.1 * p.2.2 * (∑ i : ι, Spin.sign ℝ (σ i))) := by
    funext p
    unfold partitionFunction boltzmannWeight hamiltonian
      interactionEnergy externalFieldEnergy
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    congr 1
    ring
  rw [h_eq]
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine analyticAt_rexp.comp ?_
  -- Linear combination of polynomials in (β, J, h).
  have h_β : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.1) (β, J, h) := analyticAt_fst
  have h_snd : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2) (β, J, h) := analyticAt_snd
  have h_J : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.1) (β, J, h) :=
    analyticAt_fst.comp h_snd
  have h_h : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) (β, J, h) :=
    analyticAt_snd.comp h_snd
  exact ((h_β.mul h_J).mul analyticAt_const).add ((h_β.mul h_h).mul analyticAt_const)

/-- **Free energy jointly `AnalyticAt ℝ` in `(β, J, h)`** (§18.6
capstone, jointly): `f = (1/|ι|) · log Z` is real-analytic jointly
in all three Ising parameters at every point. -/
theorem freeEnergy_analyticAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => freeEnergy G ⟨p.2.1, p.2.2, p.1⟩)
      (β, J, h) := by
  have h_pos : 0 < partitionFunction G ⟨J, h, β⟩ := partitionFunction_pos G _
  set f : ℝ × ℝ × ℝ → ℝ :=
    fun p => partitionFunction G ⟨p.2.1, p.2.2, p.1⟩ with hf_def
  have h_inner : AnalyticAt ℝ f (β, J, h) :=
    partitionFunction_analyticAt_joint G β J h
  have h_f_val : f (β, J, h) = partitionFunction G ⟨J, h, β⟩ := rfl
  have h_outer : AnalyticAt ℝ Real.log (f (β, J, h)) := by
    rw [h_f_val]; exact analyticAt_log h_pos
  have h_log :
      AnalyticAt ℝ
        (fun p : ℝ × ℝ × ℝ => Real.log (f p))
        (β, J, h) := h_outer.comp h_inner
  unfold freeEnergy
  exact analyticAt_const.mul h_log

/-- **Partition function jointly `AnalyticOnNhd ℝ` over `Set.univ`**
(§18.6 extension): global form of `partitionFunction_analyticAt_joint`. -/
theorem partitionFunction_analyticOnNhd_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ × ℝ => partitionFunction G ⟨p.2.1, p.2.2, p.1⟩)
      Set.univ :=
  fun ⟨β, J, h⟩ _ => partitionFunction_analyticAt_joint G β J h

/-- **Free energy jointly `AnalyticOnNhd ℝ` over `Set.univ`** (§18.6
capstone, jointly): global form of `freeEnergy_analyticAt_joint`. -/
theorem freeEnergy_analyticOnNhd_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ × ℝ => freeEnergy G ⟨p.2.1, p.2.2, p.1⟩)
      Set.univ :=
  fun ⟨β, J, h⟩ _ => freeEnergy_analyticAt_joint G β J h

/-- **Partition function jointly `Continuous` in `(β, J, h)`** (§18.6,
direct corollary of `partitionFunction_analyticAt_joint` via
`AnalyticAt → ContinuousAt`). -/
theorem partitionFunction_continuous_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Continuous (fun p : ℝ × ℝ × ℝ => partitionFunction G ⟨p.2.1, p.2.2, p.1⟩) :=
  continuous_iff_continuousAt.mpr fun ⟨β, J, h⟩ =>
    (partitionFunction_analyticAt_joint G β J h).continuousAt

/-- **Partition function jointly `Differentiable ℝ` in `(β, J, h)`**
(§18.6, direct corollary of `partitionFunction_analyticAt_joint` via
`AnalyticAt → DifferentiableAt`). -/
theorem partitionFunction_differentiable_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Differentiable ℝ
      (fun p : ℝ × ℝ × ℝ => partitionFunction G ⟨p.2.1, p.2.2, p.1⟩) :=
  fun ⟨β, J, h⟩ => (partitionFunction_analyticAt_joint G β J h).differentiableAt

/-- **Free energy jointly `Continuous` in `(β, J, h)`** (§18.6,
direct corollary of `freeEnergy_analyticAt_joint`). -/
theorem freeEnergy_continuous_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Continuous (fun p : ℝ × ℝ × ℝ => freeEnergy G ⟨p.2.1, p.2.2, p.1⟩) :=
  continuous_iff_continuousAt.mpr fun ⟨β, J, h⟩ =>
    (freeEnergy_analyticAt_joint G β J h).continuousAt

/-- **Free energy jointly `Differentiable ℝ` in `(β, J, h)`** (§18.6,
direct corollary of `freeEnergy_analyticAt_joint`). -/
theorem freeEnergy_differentiable_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Differentiable ℝ
      (fun p : ℝ × ℝ × ℝ => freeEnergy G ⟨p.2.1, p.2.2, p.1⟩) :=
  fun ⟨β, J, h⟩ => (freeEnergy_analyticAt_joint G β J h).differentiableAt

/-- **Numerator of correlation function jointly `AnalyticAt ℝ` in
`(β, J, h)`**: the unnormalised expectation
`∑_σ spinProduct A σ · boltzmannWeight G p σ`, viewed as a function
of `(β, J, h)`, is real-analytic jointly. Each summand is
`(constant in (β, J, h)) · exp(polynomial in (β, J, h))`. -/
theorem correlation_numerator_analyticAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ =>
        ∑ σ : Config ι, spinProduct A σ *
          boltzmannWeight G ⟨p.2.1, p.2.2, p.1⟩ σ)
      (β, J, h) := by
  have h_eq : (fun p : ℝ × ℝ × ℝ =>
      ∑ σ : Config ι, spinProduct A σ *
        boltzmannWeight G ⟨p.2.1, p.2.2, p.1⟩ σ) =
      fun p : ℝ × ℝ × ℝ => ∑ σ : Config ι, spinProduct A σ *
        Real.exp (p.1 * p.2.1 * (∑ e ∈ G.edgeFinset, edgeSpin σ e) +
          p.1 * p.2.2 * (∑ i : ι, Spin.sign ℝ (σ i))) := by
    funext p
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
    congr 1
    ring_nf
  rw [h_eq]
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine analyticAt_const.mul ?_
  refine analyticAt_rexp.comp ?_
  -- Linear combination of polynomials in (β, J, h).
  have h_β : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.1) (β, J, h) := analyticAt_fst
  have h_snd : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2) (β, J, h) := analyticAt_snd
  have h_J : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.1) (β, J, h) :=
    analyticAt_fst.comp h_snd
  have h_h : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) (β, J, h) :=
    analyticAt_snd.comp h_snd
  exact ((h_β.mul h_J).mul analyticAt_const).add ((h_β.mul h_h).mul analyticAt_const)

/-- **Correlation function jointly `AnalyticAt ℝ` in `(β, J, h)`** (§18.6
extension): for any spin subset `A` and any `(β, J, h)`,
`⟨σ_A⟩ = (∑_σ σ_A · exp(-β·H)) / Z` is real-analytic jointly in all
three Ising parameters.

Proof: `correlation = (1/Z) · numerator`, both `Z` and `numerator` are
jointly analytic (PR #1531 + helper above), and `Z > 0` lets us apply
`AnalyticAt.inv` for the reciprocal. -/
theorem correlation_analyticAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => correlation G ⟨p.2.1, p.2.2, p.1⟩ A)
      (β, J, h) := by
  unfold correlation gibbsExpectation
  have h_pos : 0 < partitionFunction G ⟨J, h, β⟩ := partitionFunction_pos G _
  set f : ℝ × ℝ × ℝ → ℝ :=
    fun p => partitionFunction G ⟨p.2.1, p.2.2, p.1⟩ with hf_def
  have h_f_val : f (β, J, h) = partitionFunction G ⟨J, h, β⟩ := rfl
  have h_inv : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      (partitionFunction G ⟨p.2.1, p.2.2, p.1⟩)⁻¹) (β, J, h) := by
    have h_Z : AnalyticAt ℝ f (β, J, h) :=
      partitionFunction_analyticAt_joint G β J h
    have h_ne : f (β, J, h) ≠ 0 := by rw [h_f_val]; exact h_pos.ne'
    exact h_Z.inv h_ne
  exact h_inv.mul (correlation_numerator_analyticAt_joint G A β J h)

/-- **Correlation function jointly `AnalyticOnNhd ℝ` over `Set.univ`**
(§18.6 extension): global form of `correlation_analyticAt_joint`. -/
theorem correlation_analyticOnNhd_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ × ℝ => correlation G ⟨p.2.1, p.2.2, p.1⟩ A)
      Set.univ :=
  fun ⟨β, J, h⟩ _ => correlation_analyticAt_joint G A β J h

/-- **Correlation function jointly `Continuous` in `(β, J, h)`** (§18.6,
direct corollary). -/
theorem correlation_continuous_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) :
    Continuous (fun p : ℝ × ℝ × ℝ => correlation G ⟨p.2.1, p.2.2, p.1⟩ A) :=
  continuous_iff_continuousAt.mpr fun ⟨β, J, h⟩ =>
    (correlation_analyticAt_joint G A β J h).continuousAt

/-- **Correlation function jointly `Differentiable ℝ` in `(β, J, h)`**
(§18.6, direct corollary). -/
theorem correlation_differentiable_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) :
    Differentiable ℝ
      (fun p : ℝ × ℝ × ℝ => correlation G ⟨p.2.1, p.2.2, p.1⟩ A) :=
  fun ⟨β, J, h⟩ => (correlation_analyticAt_joint G A β J h).differentiableAt

/-- **Magnetization jointly `Continuous` in `(β, J, h)`**: direct
corollary of `correlation_continuous_joint` at `A = {i}`. -/
theorem magnetization_continuous_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      magnetization G ⟨p.2.1, p.2.2, p.1⟩ i) := by
  unfold magnetization
  exact correlation_continuous_joint G {i}

/-- **Magnetization jointly `Differentiable ℝ` in `(β, J, h)`**:
direct corollary of `correlation_differentiable_joint` at `A = {i}`. -/
theorem magnetization_differentiable_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      magnetization G ⟨p.2.1, p.2.2, p.1⟩ i) := by
  unfold magnetization
  exact correlation_differentiable_joint G {i}

/-- **Susceptibility jointly `Continuous` in `(β, J, h)`**: finite sum of
`truncated2 = correlation {i,j} - correlation {i} · correlation {j}`,
each Continuous joint. -/
theorem susceptibility_continuous_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      susceptibility G ⟨p.2.1, p.2.2, p.1⟩ i) := by
  have heq : (fun p : ℝ × ℝ × ℝ => susceptibility G ⟨p.2.1, p.2.2, p.1⟩ i) =
      (fun p : ℝ × ℝ × ℝ =>
        ∑ j : ι, truncated2 G ⟨p.2.1, p.2.2, p.1⟩ i j) := by
    funext p
    exact susceptibility_apply G _ i
  rw [heq]
  refine continuous_finset_sum _ (fun j _ => ?_)
  unfold truncated2
  exact (correlation_continuous_joint G {i, j}).sub
    ((correlation_continuous_joint G {i}).mul
      (correlation_continuous_joint G {j}))

/-- **Susceptibility jointly `Differentiable ℝ` in `(β, J, h)`**:
finite sum of differentiable `truncated2` summands. -/
theorem susceptibility_differentiable_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      susceptibility G ⟨p.2.1, p.2.2, p.1⟩ i) := by
  have heq : (fun p : ℝ × ℝ × ℝ => susceptibility G ⟨p.2.1, p.2.2, p.1⟩ i) =
      (fun p : ℝ × ℝ × ℝ =>
        ∑ j : ι, truncated2 G ⟨p.2.1, p.2.2, p.1⟩ i j) := by
    funext p
    exact susceptibility_apply G _ i
  rw [heq]
  refine Differentiable.fun_sum (fun j _ => ?_)
  unfold truncated2
  exact (correlation_differentiable_joint G {i, j}).sub
    ((correlation_differentiable_joint G {i}).mul
      (correlation_differentiable_joint G {j}))

/-- **Correlation jointly `ContinuousAt` in `(β, J, h)`**: pointwise. -/
theorem correlation_continuousAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ => correlation G ⟨q.2.1, q.2.2, q.1⟩ A) p :=
  (correlation_continuous_joint G A).continuousAt

/-- **Correlation jointly `DifferentiableAt ℝ` in `(β, J, h)`**: pointwise. -/
theorem correlation_differentiableAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ
      (fun q : ℝ × ℝ × ℝ => correlation G ⟨q.2.1, q.2.2, q.1⟩ A) p :=
  (correlation_differentiable_joint G A).differentiableAt

/-- **Magnetization jointly `ContinuousAt` in `(β, J, h)`**: pointwise. -/
theorem magnetization_continuousAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      magnetization G ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  (magnetization_continuous_joint G i).continuousAt

/-- **Magnetization jointly `DifferentiableAt ℝ` in `(β, J, h)`**: pointwise. -/
theorem magnetization_differentiableAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      magnetization G ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  (magnetization_differentiable_joint G i).differentiableAt

/-- **Susceptibility jointly `ContinuousAt` in `(β, J, h)`**: pointwise. -/
theorem susceptibility_continuousAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      susceptibility G ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  (susceptibility_continuous_joint G i).continuousAt

/-- **Susceptibility jointly `DifferentiableAt ℝ` in `(β, J, h)`**: pointwise. -/
theorem susceptibility_differentiableAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      susceptibility G ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  (susceptibility_differentiable_joint G i).differentiableAt

/-- **Magnetization jointly `AnalyticAt ℝ` in `(β, J, h)`**:
direct corollary of `correlation_analyticAt_joint` at `A = {i}`. -/
theorem magnetization_analyticAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => magnetization G ⟨p.2.1, p.2.2, p.1⟩ i)
      (β, J, h) := by
  unfold magnetization
  exact correlation_analyticAt_joint G {i} β J h

/-- **Magnetization jointly `AnalyticOnNhd ℝ` over `Set.univ`**. -/
theorem magnetization_analyticOnNhd_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ × ℝ => magnetization G ⟨p.2.1, p.2.2, p.1⟩ i)
      Set.univ :=
  fun ⟨β, J, h⟩ _ => magnetization_analyticAt_joint G i β J h

/-- **Susceptibility jointly `AnalyticAt ℝ` in `(β, J, h)`**: finite
sum of analytic `truncated2 = corr({i,j}) − corr({i})·corr({j})`. -/
theorem susceptibility_analyticAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => susceptibility G ⟨p.2.1, p.2.2, p.1⟩ i)
      (β, J, h) := by
  have heq : (fun p : ℝ × ℝ × ℝ =>
        susceptibility G ⟨p.2.1, p.2.2, p.1⟩ i) =
      (fun p : ℝ × ℝ × ℝ =>
        ∑ j : ι, truncated2 G ⟨p.2.1, p.2.2, p.1⟩ i j) := by
    funext p
    exact susceptibility_apply G _ i
  rw [heq]
  refine Finset.analyticAt_fun_sum _ (fun j _ => ?_)
  unfold truncated2
  exact (correlation_analyticAt_joint G {i, j} β J h).sub
    ((correlation_analyticAt_joint G {i} β J h).mul
      (correlation_analyticAt_joint G {j} β J h))

/-- **Susceptibility jointly `AnalyticOnNhd ℝ` over `Set.univ`**. -/
theorem susceptibility_analyticOnNhd_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i : ι) :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ × ℝ => susceptibility G ⟨p.2.1, p.2.2, p.1⟩ i)
      Set.univ :=
  fun ⟨β, J, h⟩ _ => susceptibility_analyticAt_joint G i β J h

/-- **Numerator of gibbsExpectation jointly `AnalyticAt ℝ` in `(β, J, h)`**
for any observable `F : Config ι → ℝ`: the unnormalised expectation
`∑_σ F(σ) · boltzmannWeight G p σ` is real-analytic jointly. Each
summand is `(constant in (β, J, h)) · exp(polynomial in (β, J, h))`. -/
theorem gibbsExpectation_numerator_analyticAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (F : Config ι → ℝ) (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ =>
        ∑ σ : Config ι, F σ *
          boltzmannWeight G ⟨p.2.1, p.2.2, p.1⟩ σ)
      (β, J, h) := by
  have h_eq : (fun p : ℝ × ℝ × ℝ =>
      ∑ σ : Config ι, F σ *
        boltzmannWeight G ⟨p.2.1, p.2.2, p.1⟩ σ) =
      fun p : ℝ × ℝ × ℝ => ∑ σ : Config ι, F σ *
        Real.exp (p.1 * p.2.1 * (∑ e ∈ G.edgeFinset, edgeSpin σ e) +
          p.1 * p.2.2 * (∑ i : ι, Spin.sign ℝ (σ i))) := by
    funext p
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
    congr 1
    ring_nf
  rw [h_eq]
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine analyticAt_const.mul ?_
  refine analyticAt_rexp.comp ?_
  have h_β : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.1) (β, J, h) := analyticAt_fst
  have h_snd : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2) (β, J, h) := analyticAt_snd
  have h_J : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.1) (β, J, h) :=
    analyticAt_fst.comp h_snd
  have h_h : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) (β, J, h) :=
    analyticAt_snd.comp h_snd
  exact ((h_β.mul h_J).mul analyticAt_const).add ((h_β.mul h_h).mul analyticAt_const)

/-- **gibbsExpectation jointly `AnalyticAt ℝ` in `(β, J, h)`** (§18.6
generalisation): for any observable `F : Config ι → ℝ` and any
`(β, J, h)`,
  `⟨F⟩ = (1/Z) · ∑_σ F(σ) · exp(-β·H(σ))`
is real-analytic jointly in all three Ising parameters.

Generalises `correlation_analyticAt_joint` (PR #1536, the special case
`F = spinProduct A`) to arbitrary observables. -/
theorem gibbsExpectation_analyticAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (F : Config ι → ℝ) (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => gibbsExpectation G ⟨p.2.1, p.2.2, p.1⟩ F)
      (β, J, h) := by
  unfold gibbsExpectation
  have h_pos : 0 < partitionFunction G ⟨J, h, β⟩ := partitionFunction_pos G _
  set f : ℝ × ℝ × ℝ → ℝ :=
    fun p => partitionFunction G ⟨p.2.1, p.2.2, p.1⟩ with hf_def
  have h_f_val : f (β, J, h) = partitionFunction G ⟨J, h, β⟩ := rfl
  have h_inv : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      (partitionFunction G ⟨p.2.1, p.2.2, p.1⟩)⁻¹) (β, J, h) := by
    have h_Z : AnalyticAt ℝ f (β, J, h) :=
      partitionFunction_analyticAt_joint G β J h
    have h_ne : f (β, J, h) ≠ 0 := by rw [h_f_val]; exact h_pos.ne'
    exact h_Z.inv h_ne
  exact h_inv.mul (gibbsExpectation_numerator_analyticAt_joint G F β J h)

/-- **gibbsExpectation jointly `AnalyticOnNhd ℝ` over `Set.univ`**
(§18.6 generalisation): global form. -/
theorem gibbsExpectation_analyticOnNhd_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (F : Config ι → ℝ) :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ × ℝ => gibbsExpectation G ⟨p.2.1, p.2.2, p.1⟩ F)
      Set.univ :=
  fun ⟨β, J, h⟩ _ => gibbsExpectation_analyticAt_joint G F β J h

/-- **gibbsExpectation jointly `Continuous` in `(β, J, h)`** (§18.6
generalisation, direct corollary). -/
theorem gibbsExpectation_continuous_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (F : Config ι → ℝ) :
    Continuous (fun p : ℝ × ℝ × ℝ => gibbsExpectation G ⟨p.2.1, p.2.2, p.1⟩ F) :=
  continuous_iff_continuousAt.mpr fun ⟨β, J, h⟩ =>
    (gibbsExpectation_analyticAt_joint G F β J h).continuousAt

/-- **gibbsExpectation jointly `Differentiable ℝ` in `(β, J, h)`**
(§18.6 generalisation, direct corollary). -/
theorem gibbsExpectation_differentiable_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (F : Config ι → ℝ) :
    Differentiable ℝ
      (fun p : ℝ × ℝ × ℝ => gibbsExpectation G ⟨p.2.1, p.2.2, p.1⟩ F) :=
  fun ⟨β, J, h⟩ => (gibbsExpectation_analyticAt_joint G F β J h).differentiableAt

/-- **partitionFunction Continuous in `β` at general `h`** (§18.6,
direct corollary of `partitionFunction_analyticAt_beta_general_h`). -/
theorem partitionFunction_continuous_beta_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J h : ℝ) :
    Continuous (fun β' : ℝ => partitionFunction G ⟨J, h, β'⟩) :=
  continuous_iff_continuousAt.mpr fun β =>
    (partitionFunction_analyticAt_beta_general_h G J h β).continuousAt

/-- **partitionFunction Differentiable in `β` at general `h`** (§18.6). -/
theorem partitionFunction_differentiable_beta_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J h : ℝ) :
    Differentiable ℝ (fun β' : ℝ => partitionFunction G ⟨J, h, β'⟩) :=
  fun β => (partitionFunction_analyticAt_beta_general_h G J h β).differentiableAt

/-- **partitionFunction Continuous in `J` at general `h`** (§18.6,
direct corollary of `partitionFunction_analyticAt_J_general_h`). -/
theorem partitionFunction_continuous_J_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β h : ℝ) :
    Continuous (fun J' : ℝ => partitionFunction G ⟨J', h, β⟩) :=
  continuous_iff_continuousAt.mpr fun J =>
    (partitionFunction_analyticAt_J_general_h G β h J).continuousAt

/-- **partitionFunction Differentiable in `J` at general `h`** (§18.6). -/
theorem partitionFunction_differentiable_J_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β h : ℝ) :
    Differentiable ℝ (fun J' : ℝ => partitionFunction G ⟨J', h, β⟩) :=
  fun J => (partitionFunction_analyticAt_J_general_h G β h J).differentiableAt

/-- **partitionFunction Continuous in `h`** (§18.6, direct corollary of
`partitionFunction_analyticAt_h`). -/
theorem partitionFunction_continuous_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    Continuous (fun h' : ℝ => partitionFunction G ⟨J, h', β⟩) :=
  continuous_iff_continuousAt.mpr fun h =>
    (partitionFunction_analyticAt_h G J β h).continuousAt

/-- **partitionFunction Differentiable in `h`** (§18.6). -/
theorem partitionFunction_differentiable_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    Differentiable ℝ (fun h' : ℝ => partitionFunction G ⟨J, h', β⟩) :=
  fun h => (partitionFunction_analyticAt_h G J β h).differentiableAt

end IsingModel
