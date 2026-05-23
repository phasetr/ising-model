import IsingModel.Peierls.PlusBoundary

/-!
# Peierls argument — GJ Prop. 5.4.2 capstones

This module is part of the split `IsingModel.Peierls` development. It
collects the GJ-form Prop. 5.4.2 statement, its complete and exponential
variants, the connected-graph cut-edge nonempty lemma, and the
self-contained Prop. 5.4.2 capstone.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [Fintype ι] [DecidableEq ι] in
/-- The spin sign at site `i` relates to the down-indicator:
`Spin.sign ℝ (σ i) = 1 - 2 * 1_{σ_i = down}`. -/
private theorem spin_sign_eq_indicator (σ : Config ι) (i : ι) :
    Spin.sign ℝ (σ i) = 1 - 2 * (if σ i = Spin.down then (1 : ℝ) else 0) := by
  cases σ i
  · simp [Spin.sign, Spin.toSign]
  · simp [Spin.sign, Spin.toSign]; ring

/-- **Prop 5.4.2 in Glimm–Jaffe form** (complete statement).
Under + boundary conditions with `h = 0`:
`1 - ⟨σ_i⟩₊ ≤ 2 * Σ_{S: i∈S, S∩B=∅} exp(-2βJ|cut(S)|)`.

Since `⟨σ_i⟩₊ = ⟨sign(σ_i)⟩₊ = 1 - 2⟨1_{σ_i=↓}⟩₊`, we have
`1 - ⟨σ_i⟩₊ = 2⟨1_{σ_i=↓}⟩₊`, and the bound follows from
`spontaneous_magnetization_plus`.

For `β` sufficiently large, the RHS is `≤ exp(-cβ)` by the geometric
series evaluation of the contour sum. -/
theorem prop_5_4_2 (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (B : Finset ι) (i : ι)
    :
    1 - plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => Spin.sign ℝ (σ i)) ≤
    2 * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B),
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) := by
  have hZ := plusPartitionFunction_pos' G ⟨J, 0, β⟩ B
  -- Step 1: Rewrite sign in terms of indicator
  have hsign : ∀ σ : Config ι,
      Spin.sign ℝ (σ i) = 1 - 2 * (if σ i = Spin.down then (1 : ℝ) else 0) :=
    fun σ => spin_sign_eq_indicator σ i
  -- Step 2: ⟨sign⟩₊ = ⟨1 - 2·1_{↓}⟩₊
  have hexp : plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => Spin.sign ℝ (σ i)) =
      plusGibbsExpectation G ⟨J, 0, β⟩ B
        (fun σ => 1 - 2 * (if σ i = Spin.down then (1 : ℝ) else 0)) := by
    congr 1; ext σ; exact hsign σ
  rw [hexp]
  -- Step 3: 1 - ⟨1 - 2f⟩₊ = 2⟨f⟩₊
  -- Use: plusGibbsExpectation is Z₊⁻¹ * Σ (...)
  unfold plusGibbsExpectation at *
  -- Simplify: (1 - 2·ind(σ)) · w(σ) = w(σ) - 2·ind(σ)·w(σ)
  simp_rw [show ∀ σ : Config ι,
      (1 - 2 * (if σ i = Spin.down then (1 : ℝ) else 0)) *
        boltzmannWeight G ⟨J, 0, β⟩ σ =
      boltzmannWeight G ⟨J, 0, β⟩ σ -
        2 * ((if σ i = Spin.down then 1 else 0) *
          boltzmannWeight G ⟨J, 0, β⟩ σ)
    from fun σ => by ring]
  rw [Finset.sum_sub_distrib, mul_sub]
  -- Replace Z₊⁻¹ * Σ w with 1
  have hone : (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
      ∑ x ∈ plusConfigs B, boltzmannWeight G ⟨J, 0, β⟩ x = 1 :=
    inv_mul_cancel₀ hZ.ne'
  rw [hone]
  -- Goal: 1 - (1 - Z₊⁻¹ * 2·Σ ind·w) ≤ 2 * Σ exp(...)
  -- = Z₊⁻¹ * 2·Σ ind·w ≤ 2 * Σ exp(...)
  -- Simplify: 1 - (1 - x) = x, where x = Z₊⁻¹ * Σ 2·ind·w = 2·⟨ind⟩₊
  set x := (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
      ∑ σ ∈ plusConfigs B,
        2 * ((if σ i = Spin.down then (1 : ℝ) else 0) *
          boltzmannWeight G ⟨J, 0, β⟩ σ)
  -- Goal: 1 - (1 - x) ≤ 2 * Σ exp(...)
  have h1x : 1 - (1 - x) = x := by ring
  rw [h1x]
  -- x = 2 * Z₊⁻¹ * Σ ind·w = 2 * ⟨ind⟩₊
  have hx : x = 2 * ((plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
      ∑ σ ∈ plusConfigs B,
        (if σ i = Spin.down then (1 : ℝ) else 0) *
          boltzmannWeight G ⟨J, 0, β⟩ σ) := by
    simp only [x, Finset.mul_sum]; ring_nf
  rw [hx]
  exact mul_le_mul_of_nonneg_left
    (spontaneous_magnetization_plus G J β B i) (by norm_num)

set_option linter.unusedDecidableInType false in
/-- Under + boundary conditions, `⟨σ_i⟩₊ ≤ 1`, so `0 ≤ 1 - ⟨σ_i⟩₊`. -/
theorem one_sub_plusExpectation_nonneg (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (B : Finset ι) (i : ι)
    :
    0 ≤ 1 - plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => Spin.sign ℝ (σ i)) := by
  have hZ := plusPartitionFunction_pos' G ⟨J, 0, β⟩ B
  unfold plusGibbsExpectation
  rw [sub_nonneg]
  -- ⟨sign⟩₊ = Z₊⁻¹ · Σ sign·w ≤ Z₊⁻¹ · Σ w = 1
  calc (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
        ∑ σ ∈ plusConfigs B,
          Spin.sign ℝ (σ i) * boltzmannWeight G ⟨J, 0, β⟩ σ
      ≤ (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
          ∑ σ ∈ plusConfigs B, boltzmannWeight G ⟨J, 0, β⟩ σ := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hZ.le)
        apply Finset.sum_le_sum; intro σ _
        have hsign : Spin.sign ℝ (σ i) ≤ 1 := by
          cases σ i <;> simp [Spin.sign, Spin.toSign]
        calc Spin.sign ℝ (σ i) * boltzmannWeight G ⟨J, 0, β⟩ σ
            ≤ 1 * boltzmannWeight G ⟨J, 0, β⟩ σ :=
              mul_le_mul_of_nonneg_right hsign (boltzmannWeight_pos G ⟨J, 0, β⟩ σ).le
          _ = boltzmannWeight G ⟨J, 0, β⟩ σ := one_mul _
    _ = 1 := inv_mul_cancel₀ hZ.ne'

/-- **Prop 5.4.2 complete form** (Glimm–Jaffe §5.4, p. 83).
Under + boundary conditions on a connected graph with `h = 0`, `J > 0`,
`β > 0`, and non-empty boundary `B`:
`0 ≤ 1 - ⟨σ_i⟩₊ ≤ 2 · (2^|V|) · exp(-2βJ)`.

The hypothesis `hcut` states that every relevant subset S has `|cut(S)| ≥ 1`.
This holds for connected graphs with non-empty boundary B, since `i ∈ S`
and `S ∩ B = ∅` imply `∅ ≠ S ≠ V`. -/
theorem prop_5_4_2_complete (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (hβ : 0 < β) (hJ : 0 < J)
    (B : Finset ι) (i : ι)
    (hcut : ∀ S : Finset ι, i ∈ S → Disjoint S B → 1 ≤ (cutEdges G S).card) :
    0 ≤ 1 - plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => Spin.sign ℝ (σ i)) ∧
    1 - plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => Spin.sign ℝ (σ i)) ≤
      2 * (2 ^ Fintype.card ι) * Real.exp (-2 * β * J) := by
  have hZ := plusPartitionFunction_pos' G ⟨J, 0, β⟩ B
  constructor
  · exact one_sub_plusExpectation_nonneg G J β B i
  · calc 1 - plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => Spin.sign ℝ (σ i))
        ≤ 2 * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B),
            Real.exp (-2 * β * J * ↑(cutEdges G S).card) :=
          prop_5_4_2 G J β B i
      _ ≤ 2 * ∑ _ ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B),
            Real.exp (-2 * β * J) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum; intro S hS
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
          apply Real.exp_le_exp_of_le
          have h1 : (1 : ℝ) ≤ ↑(cutEdges G S).card := by exact_mod_cast hcut S hS.1 hS.2
          have hβJ : 0 < β * J := mul_pos hβ hJ
          nlinarith [mul_le_mul_of_nonpos_left h1 (by linarith : -2 * β * J ≤ 0)]
      _ = 2 * (↑(Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B)).card *
            Real.exp (-2 * β * J)) := by
          congr 1; rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (2 ^ Fintype.card ι * Real.exp (-2 * β * J)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          calc ↑(Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B)).card
              ≤ ↑(Finset.univ (α := Finset ι)).card := by
                exact_mod_cast Finset.card_filter_le _ _
            _ = (2 : ℝ) ^ Fintype.card ι := by
                simp [Finset.card_univ, Fintype.card_finset]
      _ = 2 * (2 ^ Fintype.card ι) * Real.exp (-2 * β * J) := by ring

/-- **Prop 5.4.2 exponential form** (Glimm–Jaffe §5.4, p. 83).
For `0 < β` and `2^(|V|+1) · exp(-2βJ) ≤ exp(-cβ)` (satisfied for β large),
`0 ≤ 1 - ⟨σ_i⟩₊ ≤ exp(-cβ)`.

The hypothesis `hexp` captures `β ≥ β₀(|V|, J, c)` in a computation-free way.
For any `0 < c < 2J`, such `β₀` exists since `2^(|V|+1) · exp(-(2J-c)β) → 0`. -/
theorem prop_5_4_2_exp (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β c : ℝ) (hβ : 0 < β) (hJ : 0 < J)
    (B : Finset ι) (i : ι)
    (hcut : ∀ S : Finset ι, i ∈ S → Disjoint S B → 1 ≤ (cutEdges G S).card)
    (hexp : 2 * (2 ^ Fintype.card ι) * Real.exp (-2 * β * J) ≤
      Real.exp (-c * β)) :
    0 ≤ 1 - plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => Spin.sign ℝ (σ i)) ∧
    1 - plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => Spin.sign ℝ (σ i)) ≤
      Real.exp (-c * β) := by
  have hcomplete := prop_5_4_2_complete G J β hβ hJ B i hcut
  exact ⟨hcomplete.1, le_trans hcomplete.2 hexp⟩


omit [Fintype ι] in
/-- A walk from `u ∈ S` to `v ∉ S` must cross a cut edge. -/
private theorem walk_crosses_cut (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (S : Finset ι) {u v : ι}
    (hu : u ∈ S) (hv : v ∉ S) (w : G.Walk u v) :
    ∃ e ∈ cutEdges G S, True := by
  induction w with
  | nil => exact absurd hu hv
  | @cons a x _ hadj w ih =>
    by_cases hx : x ∈ S
    · exact ih hx hv
    · -- Edge {a, x} crosses S: a ∈ S, x ∉ S
      refine ⟨s(a, x), ?_, trivial⟩
      simp only [cutEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset]
      constructor
      · exact hadj
      · simp only [edgeCrosses, Sym2.lift_mk]
        simp [hu, hx]

/-- In a connected graph, `∅ ≠ S ≠ V` implies `cutEdges G S` is nonempty. -/
theorem cutEdges_nonempty_of_connected (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (hconn : G.Preconnected)
    (S : Finset ι) (hne : S.Nonempty) (hneV : S ≠ Finset.univ) :
    (cutEdges G S).Nonempty := by
  obtain ⟨u, hu⟩ := hne
  have ⟨v, hv⟩ : ∃ v, v ∉ S := by
    by_contra h; push Not at h
    exact hneV (Finset.eq_univ_iff_forall.mpr h)
  obtain ⟨w⟩ := hconn u v
  obtain ⟨e, he, _⟩ := walk_crosses_cut G S hu hv w
  exact ⟨e, he⟩

set_option linter.unusedDecidableInType false in
/-- **Prop 5.4.2 self-contained** (Glimm–Jaffe §5.4, p. 83).
For a preconnected graph with non-empty boundary `B`, `h = 0`, `J > 0`, `β > 0`,
and the exponential bound condition:
`0 ≤ 1 - ⟨σ_i⟩₊ ≤ exp(-cβ)`. -/
theorem prop_5_4_2_self_contained (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (hconn : G.Preconnected)
    (J β c : ℝ) (hβ : 0 < β) (hJ : 0 < J)
    (B : Finset ι) (hB : B.Nonempty) (i : ι)
    (hexp : 2 * (2 ^ Fintype.card ι) * Real.exp (-2 * β * J) ≤
      Real.exp (-c * β)) :
    0 ≤ 1 - plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => Spin.sign ℝ (σ i)) ∧
    1 - plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => Spin.sign ℝ (σ i)) ≤
      Real.exp (-c * β) := by
  have hcut : ∀ S : Finset ι, i ∈ S → Disjoint S B → 1 ≤ (cutEdges G S).card := by
    intro S hiS hdisj
    have hne : S.Nonempty := ⟨i, hiS⟩
    have hneV : S ≠ Finset.univ := by
      intro h; rw [h] at hdisj
      have : B = ∅ := by
        ext x; constructor
        · intro hx; exact absurd (h ▸ Finset.mem_univ x) (Finset.disjoint_right.mp hdisj hx)
        · simp
      exact hB.ne_empty this
    exact (cutEdges_nonempty_of_connected G hconn S hne hneV).card_pos
  exact prop_5_4_2_exp G J β c hβ hJ B i hcut hexp

end IsingModel
