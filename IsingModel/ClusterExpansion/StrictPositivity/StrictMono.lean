import IsingModel.ClusterExpansion.StrictPositivity.IffCharacterisations

/-!
# Cluster expansion strict positivity split — strict monotonicity and strict-positivity bundles

Part of the split cluster-expansion strict-positivity layer (Issue #1850).
-/

namespace IsingModel

open Finset

/-! ## §18.4 strict monotonicity bundle

Strict monotonicity of `vdPolymerFamilies_sum` and `polymerFreeEnergy`
in the activity `t` under the hypothesis that polymers exist. Bundle
of GJ-proposition corollaries: if at least one polymer is present, then both
`vdSum` and `polymerFreeEnergy` are strictly increasing on `[0, ∞)`. -/

/-- **`vdPolymerFamilies_sum` strict monotonicity under polymers exist**
(§18.4): for `0 ≤ s < t` and `(allPolymers G).Nonempty`,
`vdPolymerFamilies_sum G s < vdPolymerFamilies_sum G t`.

Proof: the singleton polymer family `{P}` (for any `P ∈ allPolymers G`)
contributes `t^|P| > s^|P|` strictly when `s < t` and `|P| ≥ 1`. The
remaining families contribute monotone-non-decreasing terms. -/
theorem vdPolymerFamilies_sum_lt_of_lt_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_poly : (allPolymers G).Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, s ^ P.card) <
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card := by
  obtain ⟨P, hP⟩ := h_poly
  have hP_polymer : IsPolymer G P := mem_allPolymers.mp hP
  have hP_card_pos : 0 < P.card := Finset.card_pos.mpr hP_polymer.nonempty
  have h_singleton_in : ({P} : Finset (Finset (Sym2 ι))) ∈
      vdCompatiblePolymerFamilies G := by
    rw [mem_vdCompatiblePolymerFamilies]
    refine ⟨?_, ?_⟩
    · intro Q hQ
      rw [Finset.mem_singleton] at hQ; rwa [hQ]
    · exact (isCompatiblePolymerFamilyVertexDisjoint_singleton G P).mpr hP_polymer
  apply Finset.sum_lt_sum
  · intro Γ _
    apply Finset.prod_le_prod (fun Q _ => pow_nonneg hs _)
    intro Q _
    exact pow_le_pow_left₀ hs hst.le _
  · refine ⟨{P}, h_singleton_in, ?_⟩
    rw [Finset.prod_singleton, Finset.prod_singleton]
    exact pow_lt_pow_left₀ hst hs hP_card_pos.ne'

/-- **`polymerFreeEnergy` strict monotonicity under polymers exist**
(§18.4): for `0 ≤ s < t` and `(allPolymers G).Nonempty`,
`polymerFreeEnergy G s < polymerFreeEnergy G t`. Direct corollary
of `vdPolymerFamilies_sum_lt_of_lt_of_polymers_nonempty` plus
`Real.log_lt_log` (positivity of vdSum from Step 605). -/
theorem polymerFreeEnergy_lt_of_lt_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_poly : (allPolymers G).Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    polymerFreeEnergy G s < polymerFreeEnergy G t := by
  unfold polymerFreeEnergy
  apply Real.log_lt_log
  · exact vdPolymerFamilies_sum_pos_of_nonneg G hs
  · exact vdPolymerFamilies_sum_lt_of_lt_of_polymers_nonempty G h_poly hs hst

/-- **`polymerFreeEnergy` is `StrictMonoOn (Set.Ici 0)` when polymers
exist** (§18.4 strict-mono bundle). -/
theorem polymerFreeEnergy_strictMonoOn_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_poly : (allPolymers G).Nonempty) :
    StrictMonoOn (fun t : ℝ => polymerFreeEnergy G t) (Set.Ici 0) :=
  fun _ hs _ _ hst =>
    polymerFreeEnergy_lt_of_lt_of_polymers_nonempty G h_poly hs hst

/-- **`vdPolymerFamilies_sum` is `StrictMonoOn (Set.Ici 0)` when
polymers exist** (§18.4 strict-mono bundle). -/
theorem vdPolymerFamilies_sum_strictMonoOn_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_poly : (allPolymers G).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card)
      (Set.Ici 0) :=
  fun _ hs _ _ hst =>
    vdPolymerFamilies_sum_lt_of_lt_of_polymers_nonempty G h_poly hs hst

/-! ## §18.4 strict-positivity GJ-proposition-bundle

Strict positivity of `polymerFreeEnergy`, `vdSum > 1`, and `ε > 0`
under the joint hypothesis `t > 0 ∧ allPolymers G ≠ ∅`. Direct
consequences of the iff theorems plus tanh / ferromagnetic forms. -/

/-- **`polymerFreeEnergy > 0` under `0 < t` and polymers exist**
(§18.4, strict-pos bundle): direct corollary of `polymerFreeEnergy_pos_iff`. -/
theorem polymerFreeEnergy_pos_of_t_pos_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (h_t_pos : 0 < t) (h_poly : (allPolymers G).Nonempty) :
    0 < polymerFreeEnergy G t :=
  (polymerFreeEnergy_pos_iff G h_t_pos.le).mpr ⟨h_t_pos, h_poly⟩

/-- **`vdSum > 1` under `0 < t` and polymers exist** (§18.4 strict-pos
bundle): direct corollary. -/
theorem vdPolymerFamilies_sum_gt_one_of_t_pos_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (h_t_pos : 0 < t) (h_poly : (allPolymers G).Nonempty) :
    1 < (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) := by
  rw [vdPolymerFamilies_sum_gt_one_iff_eps_pos G h_t_pos.le]
  exact (vdPolymerFamilies_sum_minus_one_pos_iff G h_t_pos.le).mpr ⟨h_t_pos, h_poly⟩

/-- **`ε > 0` under `0 < t` and polymers exist** (§18.4 strict-pos
bundle). -/
theorem vdPolymerFamilies_sum_minus_one_pos_of_t_pos_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (h_t_pos : 0 < t) (h_poly : (allPolymers G).Nonempty) :
    0 < (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) :=
  (vdPolymerFamilies_sum_minus_one_pos_iff G h_t_pos.le).mpr ⟨h_t_pos, h_poly⟩

/-! ### Tanh forms -/

/-- **`polymerFreeEnergy > 0` under `0 < tanh(β·J)` and polymers exist**
(§18.4 strict-pos bundle, tanh form). -/
theorem polymerFreeEnergy_tanh_pos_of_tanh_pos_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J))
    (h_poly : (allPolymers G).Nonempty) :
    0 < polymerFreeEnergy G (Real.tanh (β * J)) :=
  polymerFreeEnergy_pos_of_t_pos_of_polymers_nonempty G h_tanh_pos h_poly

/-- **`vdSum (tanh) > 1` under `0 < tanh(β·J)` and polymers exist**
(§18.4 strict-pos bundle, tanh form). -/
theorem vdPolymerFamilies_sum_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J))
    (h_poly : (allPolymers G).Nonempty) :
    1 < (∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  vdPolymerFamilies_sum_gt_one_of_t_pos_of_polymers_nonempty G h_tanh_pos h_poly

/-- **`ε(tanh) > 0` under `0 < tanh(β·J)` and polymers exist**
(§18.4 strict-pos bundle, tanh form). -/
theorem vdPolymerFamilies_sum_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J))
    (h_poly : (allPolymers G).Nonempty) :
    0 < (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  vdPolymerFamilies_sum_minus_one_pos_of_t_pos_of_polymers_nonempty G h_tanh_pos h_poly

/-! ### StrictMono on Set.Ioi 0 (open positive reals) -/

/-- **`polymerFreeEnergy` is `StrictMonoOn (Set.Ioi 0)` under polymers
exist** (§18.4 strict-mono bundle, open positive reals). -/
theorem polymerFreeEnergy_strictMonoOn_Ioi_zero_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_poly : (allPolymers G).Nonempty) :
    StrictMonoOn (fun t : ℝ => polymerFreeEnergy G t) (Set.Ioi 0) :=
  fun _ hs _ _ hst =>
    polymerFreeEnergy_lt_of_lt_of_polymers_nonempty G h_poly (Set.mem_Ioi.mp hs).le hst

/-- **`vdPolymerFamilies_sum` is `StrictMonoOn (Set.Ioi 0)` under
polymers exist** (§18.4 strict-mono bundle). -/
theorem vdPolymerFamilies_sum_strictMonoOn_Ioi_zero_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_poly : (allPolymers G).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card)
      (Set.Ioi 0) :=
  fun _ hs _ _ hst =>
    vdPolymerFamilies_sum_lt_of_lt_of_polymers_nonempty G h_poly (Set.mem_Ioi.mp hs).le hst


end IsingModel
