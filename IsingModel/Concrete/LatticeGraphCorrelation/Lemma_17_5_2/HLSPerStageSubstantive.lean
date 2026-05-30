import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSGeneralExhaustion
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMagAlongExConvergenceCiSup

/-!
# Substantive HLS per-stage / Λ-layer bundle

GJ-proposition-unit bundle of per-stage (`correlationAlongExhaustion`)
versions of the substantive HLS chain consumer wrappers. Built via the
pointwise inequality `correlationAlongExhaustion ≤ correlationInfinite`
(monotone convergence).

**Reference:** Glimm-Jaffe §17.5 / §5.1.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Per-stage pointwise bounds at h=0 (ferromagnetic) -/

/-- **Per-stage pair correlation ≤ infinite-volume** at h=0. -/
theorem correlationAlongExhaustion_pair_le_correlationInfinite_at_h_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (n : ℕ) (x y : Fin d → ℤ) :
    correlationAlongExhaustion (latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, y} n
      ≤ correlationInfinite (latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, y} :=
  correlationAlongExhaustion_le_correlationInfinite_latticeGraph
    d Λ (⟨J, 0, β⟩ : IsingParams ℝ) {x, y} n

/-- **Per-stage pair product ≤ infinite-volume pair product** at h=0
ferromagnetic. -/
theorem correlationAlongExhaustion_pair_product_le_correlationInfinite_pair_product_at_h_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (x₀ y₀ z : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} n *
    correlationAlongExhaustion (latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z} n
    ≤ correlationInfinite (latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
    correlationInfinite (latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z} := by
  have hx_le :=
    correlationAlongExhaustion_pair_le_correlationInfinite_at_h_zero
      Λ (J := J) (β := β) n x₀ z
  have hy_le :=
    correlationAlongExhaustion_pair_le_correlationInfinite_at_h_zero
      Λ (J := J) (β := β) n y₀ z
  have hx_nn : 0 ≤ correlationAlongExhaustion (latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} n :=
    correlationAlongExhaustion_nonneg
      (latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {x₀, z} n
  have hy_nn : 0 ≤ correlationAlongExhaustion (latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z} n :=
    correlationAlongExhaustion_nonneg
      (latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {y₀, z} n
  have h_infx_nn : 0 ≤ correlationInfinite (latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} :=
    correlationInfinite_latticeGraph_nonneg
      d Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {x₀, z}
  calc correlationAlongExhaustion (latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} n *
          correlationAlongExhaustion (latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z} n
      ≤ correlationInfinite (latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
          correlationAlongExhaustion (latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z} n :=
        mul_le_mul_of_nonneg_right hx_le hy_nn
    _ ≤ correlationInfinite (latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
          correlationInfinite (latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z} :=
        mul_le_mul_of_nonneg_left hy_le h_infx_nn

/-! ## Per-stage substantive HLS sum bound -/

/-- **Per-stage substantive HLS sum bound** at h=0 ferromagnetic + strict
high-temp via monotone bound. -/
theorem exists_K_M_perstage_substantive_hls
    {d : ℕ}
    {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) :=
  hls_substantive_bound hf hβJd_pos hβJd_lt

/-- **Per-stage clusterProperty** alias (lifted from infinite-volume). -/
theorem perstage_clusterProperty_at_h_zero
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  hls_cluster_property hf hβJd_pos hβJd_lt

/-! ## Per-stage cofinite tendsto at h=0 -/

/-- **Per-site cofinite tendsto of correlationInfinite at h=0** (canonical
alias). -/
theorem perstage_tendsto_at_h_zero
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    Filter.Tendsto (fun j : Fin d → ℤ =>
        correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}) Filter.cofinite (nhds 0) :=
  hls_tendsto_correlation hf hβJd_pos hβJd_lt i

end Ambient
end IsingModel
