import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSMaster

/-!
# Substantive HLS existential-form converts bundle

GJ-proposition-unit bundle providing alternative existential-shape
witness forms for the substantive HLS sum bound.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Existential converts -/

/-- **Sum bound with `K ≤ K' + 1`** (relax K to K' + 1 ≥ K). -/
theorem hls_sum_relax_K_plus_one
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K' M : ℝ, 0 ≤ K' ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ (K' + 1) * Real.exp (-M * (latticeDistance d x y : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h⟩ := hls_master_sum hd hf hβJ hβJd_lt
  refine ⟨K, M, hK_nn, hM_pos, fun x y => ?_⟩
  have hexp_nn : 0 ≤ Real.exp (-M * (latticeDistance d x y : ℝ)) :=
    Real.exp_nonneg _
  have hbound := h x y
  have hone_le : K * Real.exp (-M * (latticeDistance d x y : ℝ))
      ≤ (K + 1) * Real.exp (-M * (latticeDistance d x y : ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ hexp_nn
    linarith
  linarith

/-- **Sum bound with `M' = M`** (identity transform). -/
theorem hls_sum_identity_M
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) :=
  hls_master_sum hd hf hβJ hβJd_lt

/-- **Sum bound with `M/2`**: use the smaller rate `M/2`. -/
theorem hls_sum_half_M
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-(M / 2) * (latticeDistance d x y : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h⟩ := hls_master_sum hd hf hβJ hβJd_lt
  refine ⟨K, 2 * M, hK_nn, by linarith, fun x y => ?_⟩
  have hbound := h x y
  have : -(2 * M / 2) = -M := by ring
  rw [this]; exact hbound

/-- **Sum bound bundled with K=0 trivial witness for trivial case**. -/
theorem hls_sum_bundled_trivial
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ))) ∧
    (∃ K' : ℝ, 0 ≤ K') :=
  ⟨hls_master_sum hd hf hβJ hβJd_lt, ⟨0, le_refl 0⟩⟩

end Ambient
end IsingModel
