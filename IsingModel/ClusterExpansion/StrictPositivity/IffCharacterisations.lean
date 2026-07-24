import IsingModel.ClusterExpansion.StrictPositivity.TanhBounds

/-!
# Cluster expansion strict positivity split — vd-polymer-family and tanh iff characterisations

Part of the split cluster-expansion strict-positivity layer (Issue #1850).
-/

namespace IsingModel

open Finset

/-- **`vdPolymerFamilies_sum = 1 ↔ ε = 0`** (§18.4 sharpening): the
polymer-family sum equals 1 iff the activity excess `ε(t)` equals 0.
Direct corollary of `vdPolymerFamilies_sum_eq_one_add` (Step 657):
vdSum = 1 + ε, so vdSum = 1 ↔ ε = 0. -/
theorem vdPolymerFamilies_sum_eq_one_iff_eps_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) = 1 ↔
      (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) = 0 := by
  rw [vdPolymerFamilies_sum_eq_one_add]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **`vdPolymerFamilies_sum > 1 ↔ ε > 0` under `0 ≤ t`** (§18.4
sharpening): under non-negative activity, the polymer-family sum
strictly exceeds 1 iff the activity excess is strictly positive. -/
theorem vdPolymerFamilies_sum_gt_one_iff_eps_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (_ht : 0 ≤ t) :
    1 < (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) ↔
      0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card := by
  rw [vdPolymerFamilies_sum_eq_one_add]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **`ε(t) > 0 ↔ 0 < t ∧ allPolymers G ≠ ∅` under `0 ≤ t`** (§18.4
sharpening): the polymer-family activity excess is strictly positive
iff `t > 0` and at least one polymer exists. Forward: from ε > 0,
some Γ ≠ ∅ has positive product, forcing `t > 0` and a polymer
witness. Backward: any single polymer `P` gives the family `{P}` whose
contribution `t^|P| > 0` (since `|P| ≥ 1` and `t > 0`). -/
theorem vdPolymerFamilies_sum_minus_one_pos_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) ↔
      0 < t ∧ (allPolymers G).Nonempty := by
  classical
  refine ⟨?_, ?_⟩
  · intro h_eps_pos
    have h_nn : ∀ Γ' ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        (0 : ℝ) ≤ ∏ P ∈ Γ', t ^ P.card := fun Γ' _ =>
      Finset.prod_nonneg (fun P _ => pow_nonneg ht _)
    have h_ne_zero : (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) ≠ 0 := h_eps_pos.ne'
    have h_exists_ne_zero : ∃ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card ≠ 0 := by
      by_contra h_all_zero
      push Not at h_all_zero
      exact h_ne_zero ((Finset.sum_eq_zero_iff_of_nonneg h_nn).mpr h_all_zero)
    obtain ⟨Γ, hΓ_mem, hΓ_ne_zero⟩ := h_exists_ne_zero
    have hΓ_pos : 0 < ∏ P ∈ Γ, t ^ P.card :=
      lt_of_le_of_ne (h_nn Γ hΓ_mem) (Ne.symm hΓ_ne_zero)
    rw [Finset.mem_erase] at hΓ_mem
    obtain ⟨hΓ_ne_empty, hΓ_in⟩ := hΓ_mem
    rw [mem_vdCompatiblePolymerFamilies] at hΓ_in
    obtain ⟨hΓ_sub, _⟩ := hΓ_in
    obtain ⟨P, hP_in_Γ⟩ := Finset.nonempty_iff_ne_empty.mpr hΓ_ne_empty
    have hP_polymer : IsPolymer G P :=
      mem_allPolymers.mp (hΓ_sub hP_in_Γ)
    have hP_card_pos : 0 < P.card := Finset.card_pos.mpr hP_polymer.nonempty
    -- The product ∏_Q t^|Q| > 0 means each t^|Q| ≠ 0, so t ≠ 0.
    have h_prod_pos : 0 < ∏ Q ∈ Γ, t ^ Q.card := hΓ_pos
    have h_t_pos : 0 < t := by
      by_contra h_t_not_pos
      push Not at h_t_not_pos
      have h_t_zero : t = 0 := le_antisymm h_t_not_pos ht
      have : (∏ Q ∈ Γ, t ^ Q.card) = 0 := by
        apply Finset.prod_eq_zero hP_in_Γ
        rw [h_t_zero, zero_pow hP_card_pos.ne']
      linarith
    refine ⟨h_t_pos, ?_⟩
    exact ⟨P, mem_allPolymers.mpr hP_polymer⟩
  · rintro ⟨h_t_pos, P, hP_in⟩
    have hP_polymer : IsPolymer G P := mem_allPolymers.mp hP_in
    -- Γ := {P} contributes t^|P| > 0.
    have h_singleton_in : ({P} : Finset (Finset (Sym2 ι))) ∈
        (vdCompatiblePolymerFamilies G).erase ∅ := by
      rw [Finset.mem_erase, mem_vdCompatiblePolymerFamilies]
      refine ⟨?_, ?_, ?_⟩
      · exact Finset.singleton_ne_empty P
      · intro Q hQ
        rw [Finset.mem_singleton] at hQ
        rwa [hQ, mem_allPolymers]
      · exact (isCompatiblePolymerFamilyVertexDisjoint_singleton G P).mpr hP_polymer
    have h_contrib_pos : 0 < ∏ Q ∈ ({P} : Finset (Finset (Sym2 ι))), t ^ Q.card := by
      rw [Finset.prod_singleton]
      exact pow_pos h_t_pos _
    have h_others_nn : ∀ Γ ∈ ((vdCompatiblePolymerFamilies G).erase ∅).erase {P},
        (0 : ℝ) ≤ ∏ Q ∈ Γ, t ^ Q.card := fun Γ _ =>
      Finset.prod_nonneg (fun _ _ => pow_nonneg ht _)
    rw [← Finset.sum_erase_add _ _ h_singleton_in]
    have h_others_sum_nn : 0 ≤ ∑ Γ ∈ ((vdCompatiblePolymerFamilies G).erase ∅).erase {P},
        ∏ Q ∈ Γ, t ^ Q.card :=
      Finset.sum_nonneg h_others_nn
    linarith

/-- **`ε(t) = 0 ↔ t = 0 ∨ allPolymers G = ∅` under `0 ≤ t`** (§18.4
sharpening): contrapositive of the strict-positivity characterisation. -/
theorem vdPolymerFamilies_sum_minus_one_eq_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) = 0 ↔
      t = 0 ∨ allPolymers G = ∅ := by
  have h_pos_iff := vdPolymerFamilies_sum_minus_one_pos_iff G ht
  have h_nn : 0 ≤ ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, t ^ P.card :=
    vdPolymerFamilies_sum_minus_one_nonneg_of_nonneg G ht
  constructor
  · intro h_zero
    by_contra h_neg
    push Not at h_neg
    obtain ⟨h_t_ne, h_poly_ne⟩ := h_neg
    have h_t_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm h_t_ne)
    have : 0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card := h_pos_iff.mpr ⟨h_t_pos, h_poly_ne⟩
    linarith
  · rintro (h_t_zero | h_poly_empty)
    · -- t = 0: each Γ ≠ ∅ has some polymer P with |P| ≥ 1, so 0^|P| = 0.
      apply Finset.sum_eq_zero
      intro Γ hΓ
      rw [Finset.mem_erase] at hΓ
      obtain ⟨hΓ_ne, hΓ_in⟩ := hΓ
      rw [mem_vdCompatiblePolymerFamilies] at hΓ_in
      obtain ⟨hΓ_sub, _⟩ := hΓ_in
      obtain ⟨P, hP⟩ := Finset.nonempty_iff_ne_empty.mpr hΓ_ne
      have hP_polymer : IsPolymer G P := mem_allPolymers.mp (hΓ_sub hP)
      have hP_pos : 0 < P.card := Finset.card_pos.mpr hP_polymer.nonempty
      apply Finset.prod_eq_zero hP
      rw [h_t_zero, zero_pow hP_pos.ne']
    · -- allPolymers G = ∅ ⇒ vdCompatiblePolymerFamilies G ⊆ {∅}.
      apply Finset.sum_eq_zero
      intro Γ hΓ
      rw [Finset.mem_erase] at hΓ
      obtain ⟨hΓ_ne, hΓ_in⟩ := hΓ
      rw [mem_vdCompatiblePolymerFamilies] at hΓ_in
      obtain ⟨hΓ_sub, _⟩ := hΓ_in
      exfalso
      obtain ⟨P, hP⟩ := Finset.nonempty_iff_ne_empty.mpr hΓ_ne
      have : P ∈ allPolymers G := hΓ_sub hP
      rw [h_poly_empty] at this
      exact Finset.notMem_empty P this

/-- **`polymerFreeEnergy > 0 ↔ 0 < t ∧ allPolymers G ≠ ∅` under `0 ≤ t`**
(§18.4 sharpening): direct corollary combining
`polymerFreeEnergy_pos_iff_eps_pos` (PR #1548) and
`vdPolymerFamilies_sum_minus_one_pos_iff` (above). -/
theorem polymerFreeEnergy_pos_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < polymerFreeEnergy G t ↔
      0 < t ∧ (allPolymers G).Nonempty := by
  rw [polymerFreeEnergy_pos_iff_eps_pos G ht]
  exact vdPolymerFamilies_sum_minus_one_pos_iff G ht

/-- **`polymerFreeEnergy = 0 ↔ t = 0 ∨ allPolymers G = ∅` under `0 ≤ t`**
(§18.4 sharpening). -/
theorem polymerFreeEnergy_eq_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    polymerFreeEnergy G t = 0 ↔ t = 0 ∨ allPolymers G = ∅ := by
  rw [polymerFreeEnergy_eq_zero_iff_eps_eq_zero G ht]
  exact vdPolymerFamilies_sum_minus_one_eq_zero_iff G ht

/-! ## Tanh-substituted forms of the iff characterisations -/

/-- **`ε(tanh) > 0 ↔ 0 < tanh(β·J) ∧ allPolymers G ≠ ∅`** (§18.4
sharpening, tanh form). -/
theorem vdPolymerFamilies_sum_minus_one_tanh_pos_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧ (allPolymers G).Nonempty :=
  vdPolymerFamilies_sum_minus_one_pos_iff G (real_tanh_nonneg hβJ)

/-- **`ε(tanh) = 0 ↔ tanh = 0 ∨ allPolymers G = ∅`** (§18.4 sharpening,
tanh form). -/
theorem vdPolymerFamilies_sum_minus_one_tanh_eq_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 ↔
      Real.tanh (β * J) = 0 ∨ allPolymers G = ∅ :=
  vdPolymerFamilies_sum_minus_one_eq_zero_iff G (real_tanh_nonneg hβJ)

/-- **`polymerFreeEnergy > 0 ↔ 0 < tanh(β·J) ∧ allPolymers G ≠ ∅`**
(§18.4 sharpening, tanh form). -/
theorem polymerFreeEnergy_tanh_pos_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < polymerFreeEnergy G (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧ (allPolymers G).Nonempty :=
  polymerFreeEnergy_pos_iff G (real_tanh_nonneg hβJ)

/-- **`polymerFreeEnergy = 0 ↔ tanh = 0 ∨ allPolymers G = ∅`** (§18.4
sharpening, tanh form). -/
theorem polymerFreeEnergy_tanh_eq_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    polymerFreeEnergy G (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨ allPolymers G = ∅ :=
  polymerFreeEnergy_eq_zero_iff G (real_tanh_nonneg hβJ)

/-- **`vdPolymerFamilies_sum > 1 ↔ 0 < tanh(β·J) ∧ allPolymers G ≠ ∅`**
(§18.4 sharpening, tanh form). -/
theorem vdPolymerFamilies_sum_tanh_gt_one_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 < (∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧ (allPolymers G).Nonempty := by
  rw [vdPolymerFamilies_sum_gt_one_iff_eps_pos G (real_tanh_nonneg hβJ)]
  exact vdPolymerFamilies_sum_minus_one_pos_iff G (real_tanh_nonneg hβJ)

/-- **`vdPolymerFamilies_sum = 1 ↔ tanh = 0 ∨ allPolymers G = ∅`**
(§18.4 sharpening, tanh form). -/
theorem vdPolymerFamilies_sum_tanh_eq_one_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨ allPolymers G = ∅ := by
  rw [vdPolymerFamilies_sum_eq_one_iff_eps_eq_zero]
  exact vdPolymerFamilies_sum_minus_one_eq_zero_iff G (real_tanh_nonneg hβJ)


end IsingModel
