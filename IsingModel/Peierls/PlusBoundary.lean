import IsingModel.Peierls.DownSpinsMagnetization

/-!
# Peierls argument — `+` boundary conditions

This module is part of the split `IsingModel.Peierls` development. It
defines the restricted partition function and Gibbs expectation under
`+` boundary conditions and proves the contour-sum bound on the
spontaneous magnetization in the boundary-restricted ensemble.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-- Configurations satisfying + boundary conditions on a set `B`. -/
def plusConfigs (B : Finset ι) : Finset (Config ι) :=
  Finset.univ.filter (fun σ => ∀ b ∈ B, σ b = Spin.up)

/-- The restricted partition function under + boundary conditions. -/
noncomputable def plusPartitionFunction (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (B : Finset ι) : ℝ :=
  ∑ σ ∈ plusConfigs B, boltzmannWeight G p σ

/-- The restricted Gibbs expectation under + boundary conditions. -/
noncomputable def plusGibbsExpectation (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (B : Finset ι) (F : Config ι → ℝ) : ℝ :=
  (plusPartitionFunction G p B)⁻¹ *
    ∑ σ ∈ plusConfigs B, F σ * boltzmannWeight G p σ

/-- The all-up configuration satisfies + boundary conditions. -/
theorem allUp_mem_plusConfigs (B : Finset ι) :
    (fun _ : ι => Spin.up) ∈ plusConfigs (ι := ι) B := by
  simp [plusConfigs]

set_option linter.unusedDecidableInType false in
/-- The restricted partition function is positive. -/
theorem plusPartitionFunction_pos' (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (p : IsingParams ℝ) (B : Finset ι) :
    0 < plusPartitionFunction G p B := by
  unfold plusPartitionFunction
  exact Finset.sum_pos (fun σ _ => boltzmannWeight_pos G p σ)
    ⟨_, allUp_mem_plusConfigs B⟩

omit [DecidableEq ι] in
/-- Under + boundary conditions, if `σ_i = down` then `i ∉ B`,
and the down-spin set `S` satisfies `S ∩ B = ∅`. -/
theorem downSpins_disjoint_boundary (σ : Config ι) (B : Finset ι)
    (hbc : ∀ b ∈ B, σ b = Spin.up) :
    Disjoint (downSpins σ) B := by
  rw [Finset.disjoint_left]
  intro x hx hxB
  simp only [downSpins, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  rw [hbc x hxB] at hx
  exact absurd hx (by decide)

/-- **Prop 5.4.2: Spontaneous magnetization under + boundary conditions**.
For h = 0, J > 0, β > 0, any graph G, boundary set B, and interior site i ∉ B:
`⟨1_{σ_i = ↓}⟩₊ ≤ Σ_{S: i∈S, S∩B=∅} exp(-2βJ|cut(S)|)`.

The RHS is exponentially small in β for β sufficiently large,
establishing spontaneous magnetization `⟨σ_i⟩₊ → 1` as `β → ∞`. -/
theorem spontaneous_magnetization_plus (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (B : Finset ι) (i : ι)
    :
    plusGibbsExpectation G ⟨J, 0, β⟩ B
      (fun σ => if σ i = Spin.down then 1 else 0) ≤
    ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B),
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) := by
  have hZ := plusPartitionFunction_pos' G ⟨J, 0, β⟩ B
  -- Step 1: Bound the + expectation by a sum of Peierls-type terms
  unfold plusGibbsExpectation
  -- The numerator: Σ_{σ∈+BC} 1_{σ_i=↓} · w(σ)
  -- For each σ ∈ +BC with σ_i = ↓: downSpins σ has i ∈ it, disjoint from B,
  -- and cut(downSpins σ) = ∂σ. So 1_{σ_i=↓} ≤ Σ_{S: i∈S, S∩B=∅} 1_{cut(S)⊆∂σ}
  have hind : ∀ σ ∈ plusConfigs B,
      (if σ i = Spin.down then (1 : ℝ) else 0) ≤
      ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B),
        if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0 := by
    intro σ hσ
    simp only [plusConfigs, Finset.mem_filter] at hσ
    by_cases hi : σ i = Spin.down
    · -- σ_i = down: downSpins σ witnesses the bound
      rw [if_pos hi]
      have hmem : downSpins σ ∈ Finset.univ.filter
          (fun S : Finset ι => i ∈ S ∧ Disjoint S B) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(mem_downSpins σ i).mpr hi, downSpins_disjoint_boundary σ B hσ.2⟩
      have hcut : cutEdges G (downSpins σ) ⊆ phaseBoundary G σ :=
        le_of_eq (cutEdges_downSpins_eq_phaseBoundary G σ)
      have hnn : ∀ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B),
          (0 : ℝ) ≤ if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0 :=
        fun S _ => by by_cases h : cutEdges G S ⊆ phaseBoundary G σ <;> simp [h]
      calc (1 : ℝ) = if cutEdges G (downSpins σ) ⊆ phaseBoundary G σ then 1 else 0 :=
            (if_pos hcut).symm
        _ ≤ ∑ S ∈ Finset.univ.filter (fun S => i ∈ S ∧ Disjoint S B),
              if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0 :=
          Finset.single_le_sum hnn hmem
    · rw [if_neg hi]
      exact Finset.sum_nonneg fun S _ => by
        by_cases h : cutEdges G S ⊆ phaseBoundary G σ <;> simp [h]
  -- Step 2: multiply by w(σ) and sum → restricted Peierls bound
  have hnum : ∑ σ ∈ plusConfigs B,
      (if σ i = Spin.down then (1 : ℝ) else 0) * boltzmannWeight G ⟨J, 0, β⟩ σ ≤
    ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B),
      ∑ σ ∈ plusConfigs B,
        (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
          boltzmannWeight G ⟨J, 0, β⟩ σ := by
    calc ∑ σ ∈ plusConfigs B,
          (if σ i = Spin.down then (1 : ℝ) else 0) * boltzmannWeight G ⟨J, 0, β⟩ σ
        ≤ ∑ σ ∈ plusConfigs B,
            (∑ S ∈ Finset.univ.filter (fun S => i ∈ S ∧ Disjoint S B),
              if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
            boltzmannWeight G ⟨J, 0, β⟩ σ := by
          apply Finset.sum_le_sum; intro σ hσ
          exact mul_le_mul_of_nonneg_right (hind σ hσ)
            (boltzmannWeight_pos G ⟨J, 0, β⟩ σ).le
      _ = ∑ σ ∈ plusConfigs B,
            ∑ S ∈ Finset.univ.filter (fun S => i ∈ S ∧ Disjoint S B),
              (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
              boltzmannWeight G ⟨J, 0, β⟩ σ := by
          apply Finset.sum_congr rfl; intro σ _; rw [Finset.sum_mul]
      _ = _ := Finset.sum_comm
  -- Step 3: Restricted Peierls bound for S with S ∩ B = ∅.
  -- flipSet S preserves + BC when S ∩ B = ∅, so the Peierls involution
  -- argument works within the restricted configuration space.
  have hpeierls : ∀ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B),
      (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
        (∑ σ ∈ plusConfigs B,
          (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
          boltzmannWeight G ⟨J, 0, β⟩ σ) ≤
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    -- Each conditional summand ≤ exp(-2βJ|cut(S)|) · w(σ^S)
    have hfactor : ∀ σ ∈ plusConfigs B,
        (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
          boltzmannWeight G ⟨J, 0, β⟩ σ ≤
        Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
          boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ) := by
      intro σ _
      by_cases hsub : cutEdges G S ⊆ phaseBoundary G σ
      · simp only [if_pos hsub, one_mul]
        exact le_of_eq (boltzmannWeight_flipSet_ratio G J β S σ hsub)
      · simp only [if_neg hsub, zero_mul]
        exact mul_nonneg (Real.exp_nonneg _) (boltzmannWeight_pos G ⟨J, 0, β⟩ _).le
    -- flipSet S maps +BC to +BC when S ∩ B = ∅
    have hflip_bc : ∀ σ ∈ plusConfigs B,
        Config.flipSet S σ ∈ plusConfigs B := by
      intro σ hσ
      simp only [plusConfigs, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      intro b hb
      simp only [Config.flipSet]
      rw [if_neg (Finset.disjoint_left.mp hS.2 · hb)]
      exact hσ b hb
    -- Sum both sides
    calc (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
          (∑ σ ∈ plusConfigs B,
            (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
            boltzmannWeight G ⟨J, 0, β⟩ σ)
        ≤ (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
            (∑ σ ∈ plusConfigs B,
              Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
              boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun σ hσ => hfactor σ hσ)
            (inv_nonneg.mpr hZ.le)
      _ = (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
            (Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
              ∑ σ ∈ plusConfigs B,
                boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ)) := by
          congr 1; rw [Finset.mul_sum]
      _ ≤ (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
            (Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
              plusPartitionFunction G ⟨J, 0, β⟩ B) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hZ.le)
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          -- Σ_{σ∈+BC} w(σ^S) ≤ Z₊ since σ^S ∈ +BC and the map is injective
          unfold plusPartitionFunction
          have : (plusConfigs B).image (Config.flipSet S) ⊆ plusConfigs B :=
            Finset.image_subset_iff.mpr (fun σ hσ => hflip_bc σ hσ)
          calc ∑ σ ∈ plusConfigs B, boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ)
              = ∑ σ ∈ (plusConfigs B).image (Config.flipSet S),
                  boltzmannWeight G ⟨J, 0, β⟩ σ := by
                rw [Finset.sum_image fun σ₁ _ σ₂ _ h => Config.flipSet_injective S h]
            _ ≤ ∑ σ ∈ plusConfigs B, boltzmannWeight G ⟨J, 0, β⟩ σ :=
                Finset.sum_le_sum_of_subset_of_nonneg this
                  (fun σ _ _ => (boltzmannWeight_pos G ⟨J, 0, β⟩ σ).le)
      _ = Real.exp (-2 * β * J * ↑(cutEdges G S).card) := by
          field_simp [hZ.ne']
  -- Combine: Z₊⁻¹ · numerator ≤ Σ_S exp(...)
  calc (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
        (∑ σ ∈ plusConfigs B,
          (if σ i = Spin.down then (1 : ℝ) else 0) * boltzmannWeight G ⟨J, 0, β⟩ σ)
      ≤ (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
          (∑ S ∈ Finset.univ.filter (fun S => i ∈ S ∧ Disjoint S B),
            ∑ σ ∈ plusConfigs B,
              (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
              boltzmannWeight G ⟨J, 0, β⟩ σ) :=
        mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr hZ.le)
    _ = ∑ S ∈ Finset.univ.filter (fun S => i ∈ S ∧ Disjoint S B),
          (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
          (∑ σ ∈ plusConfigs B,
            (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
            boltzmannWeight G ⟨J, 0, β⟩ σ) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ S ∈ Finset.univ.filter (fun S => i ∈ S ∧ Disjoint S B),
          Real.exp (-2 * β * J * ↑(cutEdges G S).card) :=
        Finset.sum_le_sum hpeierls

end IsingModel
