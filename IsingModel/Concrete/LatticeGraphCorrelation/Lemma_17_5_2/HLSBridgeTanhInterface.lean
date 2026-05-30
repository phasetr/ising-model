import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeConvenience

/-!
# HLS bridge tanh + pseudoMassG-direct interface bundle

GJ-proposition-unit bundle of tanh-direct and pseudoMassG-direct interface
variants for the HLS bridge constructors. Builds on the tanh-input variant
in HLSBridgeFromSimonLieb.lean (#3188) and the convenience layer (#3192).

**Reference:** Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel
namespace Ambient

open Real

/-! ## Ferromagnetic tanh-direct end-to-end constructor -/

/-- **`PseudoMassLatticeDistanceBridge` from tanh-input adjacent +
ferromagnetic predicate**. -/
def PseudoMassLatticeDistanceBridge_of_simonLieb_tanh_ferromagnetic
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
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
  have h2d_nn : (0 : ℝ) ≤ 2 * d := by positivity
  have hβJ_pos : 0 < β * J := by
    by_contra h
    push Not at h
    have : β * J * (2 * d) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h h2d_nn
    linarith
  PseudoMassLatticeDistanceBridge_of_simonLieb_smallReg_tanh_adjacent
    hα hr d hf.hJ hf.hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate_sl hMrate_htep
    h_corr_small h_adj_tanh

/-- **HLS sum existential from tanh-input + ferromagnetic predicate**. -/
theorem tsum_correlationInfinite_pair_product_le_const_of_simonLieb_tanh_ferromagnetic
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
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
    (PseudoMassLatticeDistanceBridge_of_simonLieb_tanh_ferromagnetic
      hα hr d hf hβJd_pos hβJd_le hM_pos hMrate_sl hMrate_htep
      h_corr_small h_adj_tanh)
    x₀ y₀

/-! ## tanh-input zero-anchor specializations -/

/-- **tanh-input HLS sum at the zero anchor `(0, 0)`**. -/
theorem tsum_correlationInfinite_pair_product_zero_anchor_le_const_of_simonLieb_tanh
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
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
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_const_of_simonLieb_tanh_ferromagnetic
    hα hr d hαd hf hβJd_pos hβJd_le hM_pos hMrate_sl hMrate_htep
    h_corr_small h_adj_tanh 0 0

/-- **tanh-input HLS sum at diagonal `(x₀, x₀)`**. -/
theorem tsum_correlationInfinite_pair_product_diagonal_le_const_of_simonLieb_tanh
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
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
    (x₀ : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_const_of_simonLieb_tanh_ferromagnetic
    hα hr d hαd hf hβJd_pos hβJd_le hM_pos hMrate_sl hMrate_htep
    h_corr_small h_adj_tanh x₀ x₀

/-! ## tanh-input translation + antipode variants -/

/-- **tanh-input HLS sum at translated anchor `(x₀ + v, y₀ + v)`**. -/
theorem tsum_correlationInfinite_pair_product_translated_anchor_le_const_of_simonLieb_tanh
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
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
    (x₀ y₀ v : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              {x₀ + v, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              {y₀ + v, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_const_of_simonLieb_tanh_ferromagnetic
    hα hr d hαd hf hβJd_pos hβJd_le hM_pos hMrate_sl hMrate_htep
    h_corr_small h_adj_tanh (x₀ + v) (y₀ + v)

/-- **tanh-input HLS sum at antipode `(v, -v)`**. -/
theorem tsum_correlationInfinite_pair_product_antipode_le_const_of_simonLieb_tanh
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
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
    (v : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {v, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {-v, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_const_of_simonLieb_tanh_ferromagnetic
    hα hr d hαd hf hβJd_pos hβJd_le hM_pos hMrate_sl hMrate_htep
    h_corr_small h_adj_tanh v (-v)

/-! ## simonLiebRate ↔ highTempExpRate comparison helpers -/

/-- **`M ≤ simonLiebRate β J d / 2 ∧ M ≤ highTempExpRate β J` from
explicit bounds**. -/
theorem M_le_both_rates_of {β J M : ℝ} {d : ℕ}
    (hM_sl : M ≤ simonLiebRate β J d / 2)
    (hM_htep : M ≤ highTempExpRate β J) :
    M ≤ simonLiebRate β J d / 2 ∧ M ≤ highTempExpRate β J :=
  ⟨hM_sl, hM_htep⟩

/-- **Tanh-input bridge from joint rate bound**. -/
def PseudoMassLatticeDistanceBridge_of_simonLieb_tanh_ferromagnetic_joint_rate
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate_both : M ≤ simonLiebRate β J d / 2 ∧ M ≤ highTempExpRate β J)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_tanh : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w) :
    PseudoMassLatticeDistanceBridge hα hr d J β :=
  PseudoMassLatticeDistanceBridge_of_simonLieb_tanh_ferromagnetic
    hα hr d hf hβJd_pos hβJd_le hM_pos hMrate_both.1 hMrate_both.2
    h_corr_small h_adj_tanh

end Ambient
end IsingModel
