import IsingModel.ClusterExpansion.GraphCases

/-!
# Cluster expansion strict positivity and monotonicity wrappers

Mechanical child split from `ClusterExpansion.lean`.
-/

namespace IsingModel

open Finset

/-! ## Tanh-substituted forms of the new strict / iff polymerFreeEnergy bounds -/

/-- **`polymerFreeEnergy < ε(tanh) ↔ ε(tanh) > 0` under `0 ≤ β·J`** (§18.4
sharpening, tanh form): tanh-substituted form of
`polymerFreeEnergy_lt_eps_iff_eps_pos`. -/
theorem polymerFreeEnergy_tanh_lt_eps_iff_eps_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    polymerFreeEnergy G (Real.tanh (β * J)) <
        ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_lt_eps_iff_eps_pos G (real_tanh_nonneg hβJ)

/-- **`polymerFreeEnergy = 0 ↔ ε(tanh) = 0` under `0 ≤ β·J`** (§18.4
sharpening, tanh form). -/
theorem polymerFreeEnergy_tanh_eq_zero_iff_eps_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    polymerFreeEnergy G (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  polymerFreeEnergy_eq_zero_iff_eps_eq_zero G (real_tanh_nonneg hβJ)

/-- **`0 < polymerFreeEnergy ↔ 0 < ε(tanh)` under `0 ≤ β·J`** (§18.4
sharpening, tanh form). -/
theorem polymerFreeEnergy_tanh_pos_iff_eps_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < polymerFreeEnergy G (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_pos_iff_eps_pos G (real_tanh_nonneg hβJ)

/-- **`polymerFreeEnergy < ε(tanh) when ε(tanh) > 0` under `0 ≤ β·J`**
(§18.4 sharpening, tanh form). -/
theorem polymerFreeEnergy_tanh_lt_eps_of_eps_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (_ : 0 ≤ β * J)
    (h_eps_pos : 0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    polymerFreeEnergy G (Real.tanh (β * J)) <
      ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_lt_eps_of_eps_pos G h_eps_pos

/-- **Connected G(ω) for n=2 ↔ incompatibility of the pair** (§18.4
sharpening): for `ω : Fin 2 → polymers`, the index-side incompatibility
graph `polymerSeqIncompatibilityGraph ω` is `Connected` iff
`PolymersIncompatible (ω 0) (ω 1)`. Provides an explicit
characterisation linking the filter-connected form (PR #1521) to the
existing pair Ursell formula (Step 585). -/
theorem polymerSeqIncompatibilityGraph_two_connected_iff_incompatible
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ω : Fin 2 → Finset (Sym2 ι)) :
    (polymerSeqIncompatibilityGraph ω).Connected ↔
      PolymersIncompatible (ω 0) (ω 1) := by
  refine ⟨?_, ?_⟩
  · -- Forward: Connected ⇒ Adj 0 1 ⇒ incompatibility (use contrapositive).
    intro h_conn
    by_contra h_compat
    -- If not incompatible, graph has no edges; 0 and 1 not reachable.
    have h_no_adj : ∀ a b : Fin 2,
        ¬ (polymerSeqIncompatibilityGraph ω).Adj a b := by
      intro a b hab
      rw [polymerSeqIncompatibilityGraph_adj] at hab
      obtain ⟨hne, hincompat⟩ := hab
      -- a, b ∈ Fin 2 and a ≠ b. So {a, b} = {0, 1}.
      fin_cases a <;> fin_cases b <;>
        first
          | exact hne rfl
          | exact h_compat hincompat
          | exact h_compat hincompat.symm
    obtain ⟨w⟩ := h_conn.preconnected 0 1
    cases w with
    | cons hadj _ =>
      exact h_no_adj _ _ hadj
  · intro h_incompat
    refine { preconnected := ?_, nonempty := ⟨0⟩ }
    intro u v
    have h_adj : (polymerSeqIncompatibilityGraph ω).Adj 0 1 := by
      rw [polymerSeqIncompatibilityGraph_adj]
      exact ⟨by decide, h_incompat⟩
    have h_reach_0 : ∀ w : Fin 2,
        (polymerSeqIncompatibilityGraph ω).Reachable w 0 := by
      intro w
      fin_cases w
      · exact SimpleGraph.Reachable.refl 0
      · exact ⟨SimpleGraph.Walk.cons h_adj.symm SimpleGraph.Walk.nil⟩
    exact (h_reach_0 u).trans (h_reach_0 v).symm

/-- **Filter-connected = filter-incompatible on `Fin 2`** (§18.4
sharpening): the cluster-sequence filter for n=2 (PR #1521) coincides
with the existing `PolymersIncompatible`-based filter (Step 597).
Direct corollary of `polymerSeqIncompatibilityGraph_two_connected_iff_incompatible`. -/
theorem mayerExpansionTerm_two_filter_connected_eq_incompat
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    (Fintype.piFinset (fun _ : Fin 2 => allPolymers G)).filter
        (fun ω => (polymerSeqIncompatibilityGraph ω).Connected) =
      (Fintype.piFinset (fun _ : Fin 2 => allPolymers G)).filter
        (fun ω => PolymersIncompatible (ω 0) (ω 1)) := by
  classical
  apply Finset.filter_congr
  intro ω _
  exact polymerSeqIncompatibilityGraph_two_connected_iff_incompatible ω

/-- **Cycle graph on `Fin 7` `DecidableRel` instance**. -/
private instance : DecidableRel (SimpleGraph.cycleGraph 7).Adj :=
  fun _ _ => decidable_of_iff _ SimpleGraph.cycleGraph_adj'.symm

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
-- `decide` on `cycleGraph 7` (7 edges, 2^7 = 128 subsets) requires
-- the raised recursion / heartbeat budgets; the larger n=8+ cases
-- exceed these limits and remain in Phase B blocker territory.
/-- **`cycleGraph 7` alternating connected-spanning sum = 6**:
the cycle on Fin 7 has 7 edges. Connected spanning subsets:
7 spanning paths (size 6 each) + the full cycle (size 7).
Sum = `7 · (-1)^6 + (-1)^7 = 7 - 1 = 6`. -/
theorem alternatingConnectedSubgraphSum_cycleGraph_seven :
    alternatingConnectedSubgraphSum (SimpleGraph.cycleGraph 7) = 6 := by
  classical
  unfold alternatingConnectedSubgraphSum
  have h_int :
      (∑ S ∈ (SimpleGraph.cycleGraph 7).edgeFinset.powerset.filter
        (fun S : Finset (Sym2 (Fin 7)) =>
          (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 7)))).Connected),
        ((-1 : ℤ) ^ S.card)) = 6 := by decide
  unfold connectedSpanningEdgeSubsets
  have h_cast :
      (∑ S ∈ (SimpleGraph.cycleGraph 7).edgeFinset.powerset.filter
          (fun S : Finset (Sym2 (Fin 7)) =>
            (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 7)))).Connected),
        ((-1 : ℝ) ^ S.card)) =
        (((∑ S ∈ (SimpleGraph.cycleGraph 7).edgeFinset.powerset.filter
            (fun S : Finset (Sym2 (Fin 7)) =>
              (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 7)))).Connected),
          ((-1 : ℤ) ^ S.card)) : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [h_cast, h_int]
  norm_num

/-- **`mayerExpansionTerm = 0` for graphs with no polymers** (§18.4
sharpening): when `allPolymers G = ∅`, the n-th Mayer term vanishes
for every `n ≥ 1` and every `t`. Reason: `piFinset (fun _ : Fin n => ∅)`
is empty for `n ≥ 1`, so the sum is trivially zero. The `n = 0` case
is already covered by `mayerExpansionTerm_zero`. Companion to
`polymerFreeEnergy_eq_zero_of_no_polymers` (Step 621): both sides of
the Mayer identity vanish when no polymers exist. -/
theorem mayerExpansionTerm_eq_zero_of_no_polymers
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_no : allPolymers G = ∅) (n : ℕ) (t : ℝ) :
    mayerExpansionTerm G n t = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact mayerExpansionTerm_zero G t
  · unfold mayerExpansionTerm
    -- n ≥ 1: piFinset (fun _ : Fin n => ∅) = ∅
    have h_empty : Fintype.piFinset (fun _ : Fin n => allPolymers G) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro ω hω
      rw [Fintype.mem_piFinset, h_no] at hω
      simpa using hω ⟨0, hn⟩
    rw [h_empty, Finset.sum_empty]

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

/-! ## §18.4 strict monotonicity bundle

Strict monotonicity of `vdPolymerFamilies_sum` and `polymerFreeEnergy`
in the activity `t` under the hypothesis that polymers exist. Bundle
of GJ-命題 corollaries: if at least one polymer is present, then both
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

/-! ## §18.4 strict-positivity GJ-命題-bundle

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

/-! ## §18.4 mayerPartialSum strict positivity / sign bundle

Sign characterisations of `mayerPartialSum` at small N: positivity at
N=1 under `t > 0` and polymers exist; non-positive contribution from
n=2 Mayer term. Bundle of corollaries derivable from existing
mayerExpansionTerm explicit forms (Steps 587, 593, 614, 637). -/

/-- **`mayerPartialSum G 1 t > 0` under `0 < t` and polymers exist**
(§18.4 strict-pos bundle): `mayerPartialSum G 1 t = ∑_{P ∈ allPolymers} t^|P|`
(Step 592), each summand `t^|P| > 0` when `t > 0` and `|P| ≥ 1`, so
the total is positive when `allPolymers G ≠ ∅`. -/
theorem mayerPartialSum_one_pos_of_t_pos_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (h_t_pos : 0 < t) (h_poly : (allPolymers G).Nonempty) :
    0 < mayerPartialSum G 1 t := by
  rw [mayerPartialSum_one]
  apply Finset.sum_pos
  · intro P hP
    have hP_polymer : IsPolymer G P := mem_allPolymers.mp hP
    have hP_card_pos : 0 < P.card := Finset.card_pos.mpr hP_polymer.nonempty
    exact pow_pos h_t_pos _
  · exact h_poly

/-- **`mayerPartialSum G 1 t ≥ 0` under `0 ≤ t`** (§18.4): total
polymer activity is non-negative. -/
theorem mayerPartialSum_one_nonneg_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ mayerPartialSum G 1 t := by
  rw [mayerPartialSum_one]
  exact Finset.sum_nonneg (fun _ _ => pow_nonneg ht _)

/-- **`mayerPartialSum G 0 t = 0`** (§18.4 sharpening):
trivial corollary of `mayerExpansionTerm_zero` and the def of
`mayerPartialSum` (sum from 0 to N+1, only the n=0 term for N=0). -/
theorem mayerPartialSum_zero_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerPartialSum G 0 t = 0 := by
  unfold mayerPartialSum
  rw [show Finset.range (0 + 1) = {0} from rfl, Finset.sum_singleton]
  exact mayerExpansionTerm_zero G t

/-! ## §18.4 ferromagnetic strict / iff bundle (J ≥ 0, β ≥ 0)

Ferromagnetic forms of the recent tanh-based iff / strict-mono /
strict-pos theorems. Convention: `J ≥ 0` and `β ≥ 0` (ferromagnetic
high-temperature regime), so `0 ≤ β·J` follows from `mul_nonneg`. -/

/-- **Ferromagnetic: `polymerFreeEnergy_tanh_lt_eps_iff_eps_pos`** under
`J ≥ 0` and `β ≥ 0`. -/
theorem polymerFreeEnergy_tanh_lt_eps_iff_eps_pos_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    polymerFreeEnergy G (Real.tanh (β * J)) <
        ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_tanh_lt_eps_iff_eps_pos G (mul_nonneg hβ hJ)

/-- **Ferromagnetic: `polymerFreeEnergy_tanh_eq_zero_iff_eps_eq_zero`** under
`J ≥ 0` and `β ≥ 0`. -/
theorem polymerFreeEnergy_tanh_eq_zero_iff_eps_eq_zero_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    polymerFreeEnergy G (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  polymerFreeEnergy_tanh_eq_zero_iff_eps_eq_zero G (mul_nonneg hβ hJ)

/-- **Ferromagnetic: `polymerFreeEnergy_tanh_pos_iff_eps_pos`** under
`J ≥ 0` and `β ≥ 0`. -/
theorem polymerFreeEnergy_tanh_pos_iff_eps_pos_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    0 < polymerFreeEnergy G (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_tanh_pos_iff_eps_pos G (mul_nonneg hβ hJ)

/-- **Ferromagnetic: `polymerFreeEnergy_tanh_pos_iff`** characterising via
`tanh > 0 ∧ polymers exist` under `J ≥ 0` and `β ≥ 0`. -/
theorem polymerFreeEnergy_tanh_pos_iff_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    0 < polymerFreeEnergy G (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧ (allPolymers G).Nonempty :=
  polymerFreeEnergy_tanh_pos_iff G (mul_nonneg hβ hJ)

/-- **Ferromagnetic: `polymerFreeEnergy_tanh_eq_zero_iff`** characterising
via `tanh = 0 ∨ no polymers` under `J ≥ 0` and `β ≥ 0`. -/
theorem polymerFreeEnergy_tanh_eq_zero_iff_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    polymerFreeEnergy G (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨ allPolymers G = ∅ :=
  polymerFreeEnergy_tanh_eq_zero_iff G (mul_nonneg hβ hJ)

/-- **Ferromagnetic: `vdSum > 1 ↔ tanh > 0 ∧ polymers exist`** under
`J ≥ 0` and `β ≥ 0`. -/
theorem vdPolymerFamilies_sum_tanh_gt_one_iff_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    1 < (∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧ (allPolymers G).Nonempty :=
  vdPolymerFamilies_sum_tanh_gt_one_iff G (mul_nonneg hβ hJ)

/-- **Ferromagnetic: `vdSum = 1 ↔ tanh = 0 ∨ no polymers`** under
`J ≥ 0` and `β ≥ 0`. -/
theorem vdPolymerFamilies_sum_tanh_eq_one_iff_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨ allPolymers G = ∅ :=
  vdPolymerFamilies_sum_tanh_eq_one_iff G (mul_nonneg hβ hJ)

/-- **Ferromagnetic: `polymerFreeEnergy_tanh_lt_pow_sub_one_of_eps_pos`**
under `J ≥ 0` and `β ≥ 0`. -/
theorem polymerFreeEnergy_tanh_lt_pow_sub_one_of_eps_pos_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h_eps_pos : 0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    polymerFreeEnergy G (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^ G.edgeFinset.card - 1 :=
  polymerFreeEnergy_tanh_lt_pow_sub_one_of_eps_pos G (mul_nonneg hβ hJ) h_eps_pos

/-- **Ferromagnetic: `polymerFreeEnergy_tanh_lt_eps_of_eps_pos`** under
`J ≥ 0` and `β ≥ 0`. -/
theorem polymerFreeEnergy_tanh_lt_eps_of_eps_pos_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h_eps_pos : 0 < ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    polymerFreeEnergy G (Real.tanh (β * J)) <
      ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_tanh_lt_eps_of_eps_pos G (mul_nonneg hβ hJ) h_eps_pos

/-! ## §18.4 polymerFreeEnergy tanh monotonicity in β / J bundle

`polymerFreeEnergy(tanh(β·J))` is strictly increasing in β at fixed
`J > 0` and in J at fixed `β > 0`, when polymers exist. Proof
combines `polymerFreeEnergy_lt_of_lt_of_polymers_nonempty` (PR #1559)
with the strict monotonicity of `Real.tanh` (proved here as a local
helper from `sinh_strictMono`). -/

/-- **`Real.tanh` strict monotonicity** (project-local helper):
proved from `sinh_strictMono` via the identity
`tanh y - tanh x = sinh(y - x) / (cosh x · cosh y)` (with both cosh
positive). Mathlib doesn't yet export `Real.tanh_strictMono`. -/
private theorem real_tanh_strictMono : StrictMono Real.tanh := by
  intro x y hxy
  have hx_pos : 0 < Real.cosh x := Real.cosh_pos x
  have hy_pos : 0 < Real.cosh y := Real.cosh_pos y
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
      div_lt_div_iff₀ hx_pos hy_pos]
  -- Goal: sinh x · cosh y < sinh y · cosh x
  -- Use: sinh y · cosh x - sinh x · cosh y = sinh(y - x) > 0.
  have h_sub : Real.sinh y * Real.cosh x - Real.sinh x * Real.cosh y =
      Real.sinh (y - x) := by rw [Real.sinh_sub]; ring
  have h_sinh_pos : 0 < Real.sinh (y - x) := by
    rw [show (0 : ℝ) = Real.sinh 0 from Real.sinh_zero.symm]
    exact Real.sinh_strictMono (sub_pos.mpr hxy)
  linarith

/-- **`polymerFreeEnergy(tanh(β·J))` strictly increasing in β at fixed
`J > 0` under polymers exist** (§18.4 tanh-monotonicity bundle). -/
theorem polymerFreeEnergy_tanh_lt_of_lt_in_beta_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_poly : (allPolymers G).Nonempty)
    {β₁ β₂ J : ℝ} (hβ₁ : 0 ≤ β₁) (hJ : 0 < J) (hβ : β₁ < β₂) :
    polymerFreeEnergy G (Real.tanh (β₁ * J)) <
      polymerFreeEnergy G (Real.tanh (β₂ * J)) := by
  apply polymerFreeEnergy_lt_of_lt_of_polymers_nonempty G h_poly
  · exact real_tanh_nonneg (mul_nonneg hβ₁ hJ.le)
  · exact real_tanh_strictMono (mul_lt_mul_of_pos_right hβ hJ)

/-- **`polymerFreeEnergy(tanh(β·J))` strictly increasing in J at fixed
`β > 0` under polymers exist** (§18.4 tanh-monotonicity bundle). -/
theorem polymerFreeEnergy_tanh_lt_of_lt_in_J_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_poly : (allPolymers G).Nonempty)
    {β J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hβ : 0 < β) (hJ : J₁ < J₂) :
    polymerFreeEnergy G (Real.tanh (β * J₁)) <
      polymerFreeEnergy G (Real.tanh (β * J₂)) := by
  apply polymerFreeEnergy_lt_of_lt_of_polymers_nonempty G h_poly
  · exact real_tanh_nonneg (mul_nonneg hβ.le hJ₁)
  · exact real_tanh_strictMono (mul_lt_mul_of_pos_left hJ hβ)

/-- **`polymerFreeEnergy(tanh(β·J))` is `StrictMonoOn (Set.Ici 0)` in β**
under fixed `J > 0` and polymers exist (§18.4). -/
theorem polymerFreeEnergy_tanh_strictMonoOn_beta_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_poly : (allPolymers G).Nonempty)
    {J : ℝ} (hJ : 0 < J) :
    StrictMonoOn (fun β : ℝ => polymerFreeEnergy G (Real.tanh (β * J)))
      (Set.Ici 0) :=
  fun _ hβ₁ _ _ hβ =>
    polymerFreeEnergy_tanh_lt_of_lt_in_beta_of_polymers_nonempty
      G h_poly hβ₁ hJ hβ

/-- **`polymerFreeEnergy(tanh(β·J))` is `StrictMonoOn (Set.Ici 0)` in J**
under fixed `β > 0` and polymers exist (§18.4). -/
theorem polymerFreeEnergy_tanh_strictMonoOn_J_of_polymers_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_poly : (allPolymers G).Nonempty)
    {β : ℝ} (hβ : 0 < β) :
    StrictMonoOn (fun J : ℝ => polymerFreeEnergy G (Real.tanh (β * J)))
      (Set.Ici 0) :=
  fun _ hJ₁ _ _ hJ =>
    polymerFreeEnergy_tanh_lt_of_lt_in_J_of_polymers_nonempty
      G h_poly hJ₁ hβ hJ


end IsingModel
