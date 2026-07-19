import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromSimonLiebCore

/-!
# HLS bridge from Simon-Lieb: tanh-power input variants

Tanh child module of the build-speed split of `HLSBridgeFromSimonLieb`.
Provides the end-to-end bridge constructors and HLS sum consumers that take the
adjacent correlation input in the natural `tanh(β·J)^dist` form, converting to
the exponential form of the core constructors.  See the umbrella
`HLSBridgeFromSimonLieb` for the full narrative and references.
-/

namespace IsingModel
namespace Ambient

open Real

/-! ## Tanh-input variants -/

/-- **End-to-end bridge constructor from tanh-power adjacent input**.

Variant of `PseudoMassLatticeDistanceBridge_of_simonLieb_smallReg_adjacent`
taking the adjacent input in the natural `tanh(β·J)^(d(0,w))` form (= `tanh`
at `dist = 1`) and converting via Step 5.7d (`tanh^d ≤ exp(-(M·d))` from
PR #3175 at `r := 1` with `M ≤ highTempExpRate β J`). -/
def PseudoMassLatticeDistanceBridge_of_simonLieb_smallReg_tanh_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate_sl : M ≤ simonLiebRate β J d / 2)
    (hMrate_htep : M ≤ highTempExpRate β J)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_tanh : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w) :
    PseudoMassLatticeDistanceBridge hα hr d J β :=
  PseudoMassLatticeDistanceBridge_of_simonLieb_smallReg_adjacent
    hα hr d hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate_sl
    h_corr_small
    (fun w hw_eq_one => by
      have hbase := h_adj_tanh w hw_eq_one
      have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
      have hMrate_one : M * (1 : ℝ) ≤ highTempExpRate β J := by
        rw [mul_one]; exact hMrate_htep
      have h_tanh_le_exp :
          Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w ≤
            Real.exp (-(M * (IsingModel.latticeDistance d 0 w : ℝ) * 1)) :=
        tanh_pow_le_exp_neg_M_dist_r_of_M_r_le_highTempExpRate
          hβJ hMrate_one _
      have h_dist_eq : (IsingModel.latticeDistance d 0 w : ℝ) = 1 := by
        rw [hw_eq_one]; norm_cast
      have h_exp_eq :
          Real.exp (-(M * (IsingModel.latticeDistance d 0 w : ℝ) * 1)) =
            Real.exp (-M) := by
        rw [h_dist_eq]; ring_nf
      rw [h_exp_eq] at h_tanh_le_exp
      exact hbase.trans h_tanh_le_exp)

/-- **End-to-end trichotomy bridge from tanh-power adjacent input**.

This is the tanh-input analogue of
`PseudoMassLatticeDistanceBridge_of_simonLieb_trichotomy_adjacent`: it converts
the adjacent tanh-power bound to `exp (-M)` and then uses the full
adjacent/small/large Simon-Lieb trichotomy, so there is no uniform small-regime
assumption. -/
def PseudoMassLatticeDistanceBridge_of_simonLieb_trichotomy_tanh_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate_sl : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    (hMrate_htep : M ≤ highTempExpRate β J)
    (h_adj_tanh : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w) :
    PseudoMassLatticeDistanceBridge hα hr d J β :=
  PseudoMassLatticeDistanceBridge_of_simonLieb_trichotomy_adjacent
    hα hr d hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hM_le_one hMrate_sl
    (fun w hw_eq_one => by
      have hbase := h_adj_tanh w hw_eq_one
      have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
      have hMrate_one : M * (1 : ℝ) ≤ highTempExpRate β J := by
        rw [mul_one]; exact hMrate_htep
      have h_tanh_le_exp :
          Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w ≤
            Real.exp (-(M * (IsingModel.latticeDistance d 0 w : ℝ) * 1)) :=
        tanh_pow_le_exp_neg_M_dist_r_of_M_r_le_highTempExpRate
          hβJ hMrate_one _
      have h_dist_eq : (IsingModel.latticeDistance d 0 w : ℝ) = 1 := by
        rw [hw_eq_one]; norm_cast
      have h_exp_eq :
          Real.exp (-(M * (IsingModel.latticeDistance d 0 w : ℝ) * 1)) =
            Real.exp (-M) := by
        rw [h_dist_eq]; ring_nf
      rw [h_exp_eq] at h_tanh_le_exp
      exact hbase.trans h_tanh_le_exp)

/-- **HLS sum from tanh-power adjacent + Simon-Lieb inputs**. -/
theorem tsum_correlationInfinite_pair_product_le_const_of_simonLieb_tanh_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate_sl : M ≤ simonLiebRate β J d / 2)
    (hMrate_htep : M ≤ highTempExpRate β J)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_tanh : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w)
    (x₀ y₀ : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_HLS_const hα hr d hαd J β
    (PseudoMassLatticeDistanceBridge_of_simonLieb_smallReg_tanh_adjacent
      hα hr d hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate_sl hMrate_htep
      h_corr_small h_adj_tanh)
    x₀ y₀

/-- **HLS sum from tanh-power adjacent input and the full Simon-Lieb
trichotomy bridge**. -/
theorem tsum_correlationInfinite_pair_product_le_const_of_simonLieb_trichotomy_tanh_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate_sl : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    (hMrate_htep : M ≤ highTempExpRate β J)
    (h_adj_tanh : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w)
    (x₀ y₀ : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_HLS_const hα hr d hαd J β
    (PseudoMassLatticeDistanceBridge_of_simonLieb_trichotomy_tanh_adjacent
      hα hr d hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hM_le_one hMrate_sl
      hMrate_htep h_adj_tanh)
    x₀ y₀

end Ambient
end IsingModel
