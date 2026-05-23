import IsingModel.Peierls.BoltzmannPeierls

/-!
# Peierls argument — down-spin sets and magnetization bounds

This module is part of the split `IsingModel.Peierls` development. It
collects the down-spin set, the identification of its cut edges with the
phase boundary, the indicator/contour-sum inequality, Gibbs expectation
monotonicity, and the resulting spontaneous-magnetization upper bounds.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-! ## Down-spin set and phase boundary

The set of sites with spin down in a configuration σ determines a subset
whose cut edges are exactly the phase boundary. This is the key link
between spin configurations and the contour (Peierls) decomposition. -/

/-- The set of sites with spin `down` in configuration `σ`. -/
def downSpins (σ : Config ι) : Finset ι :=
  Finset.univ.filter (fun j => σ j = Spin.down)

omit [DecidableEq ι] in
/-- A site `i` is in `downSpins σ` iff `σ i = Spin.down`. -/
@[simp]
theorem mem_downSpins (σ : Config ι) (i : ι) :
    i ∈ downSpins σ ↔ σ i = Spin.down := by
  simp [downSpins]

/-- The cut edges of the down-spin set equal the phase boundary.
For any edge `{u,v}` in `cutEdges G (downSpins σ)`:
`u` has spin down, `v` has spin up, so they disagree. -/
theorem cutEdges_downSpins_eq_phaseBoundary (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (σ : Config ι) :
    cutEdges G (downSpins σ) = phaseBoundary G σ := by
  ext e
  simp only [cutEdges, phaseBoundary, Finset.mem_filter]
  refine and_congr_right fun _ => ?_
  -- Show: edgeCrosses (downSpins σ) e = true ↔ edgeDisagrees σ e = true
  refine Sym2.ind (fun u v => ?_) e
  simp only [edgeCrosses, edgeDisagrees, downSpins, Sym2.lift_mk,
    Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  cases σ u <;> cases σ v <;> simp

/-- If `σ i = Spin.down`, then `downSpins σ` is a subset containing `i`
whose cut edges are contained in the phase boundary. This witnesses
the event `σ_i = -1` in the contour decomposition. -/
theorem exists_contour_of_spin_down (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (σ : Config ι) (i : ι) (hi : σ i = Spin.down) :
    i ∈ downSpins σ ∧ cutEdges G (downSpins σ) ⊆ phaseBoundary G σ := by
  exact ⟨mem_downSpins σ i |>.mpr hi,
    le_of_eq (cutEdges_downSpins_eq_phaseBoundary G σ)⟩

/-- **Indicator inequality for the Peierls decomposition**.
The indicator of `σ_i = down` is bounded by the sum of indicators
over all subsets S containing i:
`1_{σ_i = down} ≤ Σ_{S ∋ i} 1_{cut(S) ⊆ ∂σ}`. -/
theorem indicator_spin_down_le_contour_sum (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (σ : Config ι) (i : ι) :
    (if σ i = Spin.down then (1 : ℝ) else 0) ≤
      ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
        if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0 := by
  split
  · next hi =>
    -- σ i = down: the term for S = downSpins σ contributes 1
    have hmem : downSpins σ ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S) := by
      simp [mem_downSpins, hi]
    have hsub : cutEdges G (downSpins σ) ⊆ phaseBoundary G σ :=
      le_of_eq (cutEdges_downSpins_eq_phaseBoundary G σ)
    have hterm : (if cutEdges G (downSpins σ) ⊆ phaseBoundary G σ then (1 : ℝ) else 0) = 1 :=
      if_pos hsub
    calc (1 : ℝ) = if cutEdges G (downSpins σ) ⊆ phaseBoundary G σ then 1 else 0 := hterm.symm
      _ ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
            if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0 :=
        have hnn : ∀ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
            (0 : ℝ) ≤ if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0 :=
          fun S _ => by by_cases h : cutEdges G S ⊆ phaseBoundary G σ <;> simp [h]
        Finset.single_le_sum hnn hmem
  · -- σ i ≠ down: LHS = 0, trivially ≤ sum of non-negatives
    exact Finset.sum_nonneg fun S _ => by
      by_cases h : cutEdges G S ⊆ phaseBoundary G σ <;> simp [h]

set_option linter.unusedDecidableInType false in
/-- **Gibbs expectation monotonicity**: if `F σ ≤ G σ` pointwise, then `⟨F⟩ ≤ ⟨G⟩`. -/
theorem gibbsExpectation_mono (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (p : IsingParams ℝ) (F₁ F₂ : Config ι → ℝ)
    (h : ∀ σ, F₁ σ ≤ F₂ σ) :
    gibbsExpectation G p F₁ ≤ gibbsExpectation G p F₂ := by
  unfold gibbsExpectation
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum fun σ _ =>
      mul_le_mul_of_nonneg_right (h σ) (boltzmannWeight_pos G p σ).le
  · exact inv_nonneg.mpr (partitionFunction_pos G p).le

/-- **Probability of spin down bounded by contour sum** (Glimm–Jaffe §5.4).
`⟨1_{σ_i = ↓}⟩ ≤ Σ_{S ∋ i} ⟨1_{cut(S) ⊆ ∂σ}⟩`.
This is the Gibbs-expectation form of `indicator_spin_down_le_contour_sum`. -/
theorem gibbs_spin_down_le_contour_sum (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (i : ι) :
    gibbsExpectation G ⟨J, 0, β⟩
      (fun σ => if σ i = Spin.down then 1 else 0) ≤
    ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
      gibbsExpectation G ⟨J, 0, β⟩
        (fun σ => if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) := by
  -- Step 1: ⟨1_{↓}⟩ ≤ ⟨Σ_S 1_{cut(S)⊆∂σ}⟩ by monotonicity
  calc gibbsExpectation G ⟨J, 0, β⟩ (fun σ => if σ i = Spin.down then 1 else 0)
      ≤ gibbsExpectation G ⟨J, 0, β⟩
          (fun σ => ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
            if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) :=
        gibbsExpectation_mono G ⟨J, 0, β⟩ _ _
          (indicator_spin_down_le_contour_sum G · i)
    -- Step 2: ⟨Σ_S f(S,σ)⟩ = Σ_S ⟨f(S,σ)⟩ by linearity
    _ = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
          gibbsExpectation G ⟨J, 0, β⟩
            (fun σ => if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) := by
        -- Linearity of Gibbs expectation over finite sums
        unfold gibbsExpectation
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro σ _
        rw [Finset.sum_mul]

/-- **Spontaneous magnetization bound** (Glimm–Jaffe, Prop. 5.4.2).
The probability of spin down at site `i` is bounded by the sum of
Peierls bounds over all subsets containing `i`:
`⟨1_{σ_i = ↓}⟩ ≤ Σ_{S ∋ i} exp(-2βJ|cut(S)|)`.

This is the main inequality driving the Peierls argument: for `β`
sufficiently large, the RHS is exponentially small in `β`. -/
theorem spontaneous_magnetization_bound (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (i : ι) :
    gibbsExpectation G ⟨J, 0, β⟩
      (fun σ => if σ i = Spin.down then 1 else 0) ≤
    ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) := by
  calc gibbsExpectation G ⟨J, 0, β⟩
        (fun σ => if σ i = Spin.down then 1 else 0)
      ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
          gibbsExpectation G ⟨J, 0, β⟩
            (fun σ => if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) :=
        gibbs_spin_down_le_contour_sum G J β i
    _ ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
          Real.exp (-2 * β * J * ↑(cutEdges G S).card) :=
        Finset.sum_le_sum fun S _ => peierls_bound G J β S

/-! ## + Boundary conditions

For the Peierls argument, we fix spins on a boundary set `B` to `up`.
The restricted Gibbs measure averages only over configurations with
`σ(b) = up` for all `b ∈ B`. -/

end IsingModel
