import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSSubstantiveBundle

/-!
# Substantive HLS bundle extensions

GJ-proposition-unit bundle extending the substantive HLS bundle (#3199):
correlation-form variants (via `h = 0` identity), zero-anchor / diagonal /
swap / antipode specializations, joint K extraction.

**Reference:** Glimm-Jaffe §17.5 Lemma 17.5.2.
-/

namespace IsingModel
namespace Ambient

/-! ## Correlation-form substantive HLS bound (via h=0) -/

/-- **Substantive correlation-form HLS bound at `h = 0`**.

At `h = 0`, `truncated2Infinite = correlationInfinite {i, j}`, so the
substantive tsum bound (#3199) transfers to the correlation pair-product
form. -/
theorem exists_tsum_correlationInfinite_pair_product_le_of_simonLieb_ferromagnetic
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
    exists_tsum_truncated2Infinite_prod_le_of_simonLieb_ferromagnetic_high_temp
      hf hβJd_pos hβJd_lt
  refine ⟨K, M, hK_nn, hM_pos, ?_⟩
  intro x y
  have h_t2_eq : ∀ a b : Fin d → ℤ,
      truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) a b =
      correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {a, b} := fun a b =>
    truncated2Infinite_latticeGraph_h_zero d J β a b
  have h_summand_eq : ∀ z : Fin d → ℤ,
      truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z *
      truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) y z =
      correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
      correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {y, z} := fun z => by
    rw [h_t2_eq x z, h_t2_eq y z]
  have h_t2_to_corr : (∑' z : Fin d → ℤ,
      truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z *
      truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) y z) =
      ∑' z : Fin d → ℤ,
        correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
        correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {y, z} :=
    tsum_congr h_summand_eq
  rw [← h_t2_to_corr]
  exact h_bound x y

/-! ## Specialization at zero anchor -/

/-- **Substantive HLS bound at the zero anchor `(0, 0)`**. -/
theorem exists_tsum_correlationInfinite_pair_product_zero_anchor_le_of_simonLieb_ferromagnetic
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∑' z : Fin d → ℤ,
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {0, z} *
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {0, z}
      ≤ K * Real.exp (-M * (latticeDistance d 0 0 : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
    exists_tsum_correlationInfinite_pair_product_le_of_simonLieb_ferromagnetic
      hf hβJd_pos hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, h_bound 0 0⟩

/-! ## Specialization at diagonal anchor (x₀, x₀) -/

/-- **Substantive HLS bound at the diagonal anchor `(x₀, x₀)`**. -/
theorem exists_tsum_correlationInfinite_pair_product_diagonal_le_of_simonLieb_ferromagnetic
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1)
    (x₀ : Fin d → ℤ) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∑' z : Fin d → ℤ,
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z}
      ≤ K * Real.exp (-M * (latticeDistance d x₀ x₀ : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
    exists_tsum_correlationInfinite_pair_product_le_of_simonLieb_ferromagnetic
      hf hβJd_pos hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, h_bound x₀ x₀⟩

/-! ## Swap symmetry -/

/-- **Substantive HLS bound at swapped anchor `(y₀, x₀)`**. -/
theorem exists_tsum_correlationInfinite_pair_product_swap_le_of_simonLieb_ferromagnetic
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1)
    (x₀ y₀ : Fin d → ℤ) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∑' z : Fin d → ℤ,
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z} *
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z}
      ≤ K * Real.exp (-M * (latticeDistance d y₀ x₀ : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
    exists_tsum_correlationInfinite_pair_product_le_of_simonLieb_ferromagnetic
      hf hβJd_pos hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, h_bound y₀ x₀⟩

/-! ## Antipode specialization -/

/-- **Substantive HLS bound at antipode anchor `(v, -v)`**. -/
theorem exists_tsum_correlationInfinite_pair_product_antipode_le_of_simonLieb_ferromagnetic
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1)
    (v : Fin d → ℤ) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∑' z : Fin d → ℤ,
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {v, z} *
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {-v, z}
      ≤ K * Real.exp (-M * (latticeDistance d v (-v) : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
    exists_tsum_correlationInfinite_pair_product_le_of_simonLieb_ferromagnetic
      hf hβJd_pos hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, h_bound v (-v)⟩

/-! ## Joint K extraction -/

/-- **Existential `K ≥ 0` and `M > 0` from the substantive HLS bound**
(correlation form). -/
theorem exists_K_nonneg_M_pos_substantive_hls_of_simonLieb_ferromagnetic
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M :=
  let ⟨K, M, hK_nn, hM_pos, _⟩ :=
    exists_tsum_correlationInfinite_pair_product_le_of_simonLieb_ferromagnetic
      hf hβJd_pos hβJd_lt
  ⟨K, M, hK_nn, hM_pos⟩

/-- **HLS rate `M = simonLiebRate β J d / 8` summary**. The rate `M`
returned by the substantive bound is `simonLiebRate β J d / 8` (= α / 4
with α = simonLiebRate/2). This positivity helper exposes it. -/
theorem simonLiebRate_div_eight_pos_of_strict_high_temp
    {β J : ℝ} {d : ℕ}
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1) :
    0 < simonLiebRate β J d / 8 := by
  have hSL_pos : 0 < simonLiebRate β J d := simonLiebRate_pos hβJd_pos hβJd_lt
  linarith

end Ambient
end IsingModel
