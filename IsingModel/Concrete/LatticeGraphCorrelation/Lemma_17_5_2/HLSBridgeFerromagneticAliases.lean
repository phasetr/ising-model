import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeSummary

/-!
# HLS bridge ecosystem ferromagnetic-form summary aliases

GJ-proposition-unit bundle of ferromagnetic-form summary aliases providing
cleaner / shorter access names for downstream consumers.

This file collects the simplest API access surface, keeping the
ferromagnetic predicate as the primary structural input.

**Reference:** Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel
namespace Ambient

open Real

/-! ## Ferromagnetic-form aliases (shortest API access surface) -/

/-- **Bridge (short alias for `canonical_bridge_from_simonLieb_adjacent`)**. -/
def hls_bridge_simonLieb
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    PseudoMassLatticeDistanceBridge hα hr d J β :=
  canonical_bridge_from_simonLieb_adjacent
    hα hr d hf hβJd_pos hβJd_le hM_pos hMrate h_corr_small h_adj_exp

/-- **Bridge tanh (short alias for `canonical_bridge_from_tanh_adjacent`)**. -/
def hls_bridge_tanh
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ) {J β : ℝ}
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
  canonical_bridge_from_tanh_adjacent
    hα hr d hf hβJd_pos hβJd_le hM_pos hMrate_sl hMrate_htep
    h_corr_small h_adj_tanh

/-- **HLS sum (short alias for `canonical_hls_sum`)**. -/
theorem hls_sum_simonLieb
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M))
    (x₀ y₀ : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z}
      ≤ K :=
  canonical_hls_sum
    hα hr d hαd hf hβJd_pos hβJd_le hM_pos hMrate h_corr_small h_adj_exp x₀ y₀

/-- **HLS sum tanh (short alias for `canonical_hls_sum_tanh`)**. -/
theorem hls_sum_tanh
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
  canonical_hls_sum_tanh
    hα hr d hαd hf hβJd_pos hβJd_le hM_pos hMrate_sl hMrate_htep
    h_corr_small h_adj_tanh x₀ y₀

/-- **Bound provider (short alias)**. -/
theorem hls_bound_provider
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      M * (latticeDistance d x z : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z * r :=
  canonical_bound_provider hα hr d hf hβJd_pos hβJd_le
    hM_pos hMrate h_corr_small h_adj_exp

/-- **Active provider (short alias)**. -/
theorem hls_active_provider
    {d : ℕ} {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ_pos : 0 < β * J) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
        ∈ Set.Ioo (0 : ℝ) 2 :=
  canonical_active_provider hf hβJ_pos

/-- **Zero-anchor HLS sum (short alias)**. -/
theorem hls_sum_zero_anchor
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, z}
      ≤ K :=
  canonical_hls_sum_zero_anchor
    hα hr d hαd hf hβJd_pos hβJd_le hM_pos hMrate h_corr_small h_adj_exp

/-- **Positive K extraction (short alias)**. -/
theorem hls_K_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M))
    (x₀ y₀ : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K :=
  canonical_K_pos_from_hls_sum
    hα hr d hαd hf hβJd_pos hβJd_le hM_pos hMrate h_corr_small h_adj_exp x₀ y₀

end Ambient
end IsingModel
