import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSSubstantiveExistingRate

/-!
# Substantive HLS canonical summary API

Canonical anchor and witness projections for the substantive HLS chain.
The underlying Simon-Lieb half-rate and existing full-rate constructors live in
`HLSSubstantiveSimonLieb` and `HLSSubstantiveExistingRate`; importing this
module keeps the old summary entry point available while avoiding another
monolithic bundle.

**Reference:** Glimm-Jaffe §17.5 Lemma 17.5.2.
-/

namespace IsingModel
namespace Ambient

/-! ## Anchor canonical entry points -/

/-- **Canonical zero-anchor substantive HLS bound** at `(0, 0)`. -/
theorem hls_substantive_bound_zero_anchor
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∑' z : Fin d → ℤ,
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {0, z} *
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {0, z}
      ≤ K * Real.exp (-M * (latticeDistance d 0 0 : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
    hls_substantive_bound hf hβJd_pos hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, h_bound 0 0⟩

/-- **Canonical diagonal substantive HLS bound** at `(x₀, x₀)`. -/
theorem hls_substantive_bound_diagonal
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (x₀ : Fin d → ℤ) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∑' z : Fin d → ℤ,
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z}
      ≤ K * Real.exp (-M * (latticeDistance d x₀ x₀ : ℝ)) :=
  by
    obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
      hls_substantive_bound hf hβJd_pos hβJd_lt
    exact ⟨K, M, hK_nn, hM_pos, h_bound x₀ x₀⟩

/-- **Canonical swapped-anchor substantive HLS bound** at `(y₀, x₀)`. -/
theorem hls_substantive_bound_swap
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (x₀ y₀ : Fin d → ℤ) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∑' z : Fin d → ℤ,
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z} *
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z}
      ≤ K * Real.exp (-M * (latticeDistance d y₀ x₀ : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
    hls_substantive_bound hf hβJd_pos hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, h_bound y₀ x₀⟩

/-- **Canonical antipode-anchor substantive HLS bound** at `(v, -v)`. -/
theorem hls_substantive_bound_antipode
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (v : Fin d → ℤ) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∑' z : Fin d → ℤ,
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {v, z} *
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {-v, z}
      ≤ K * Real.exp (-M * (latticeDistance d v (-v) : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
    hls_substantive_bound hf hβJd_pos hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, h_bound v (-v)⟩

/-! ## Witness canonical entry points -/

/-- **Canonical `K ≥ 0`, `M > 0` extraction** from the substantive HLS bound. -/
theorem hls_exists_K_M_substantive_bound
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M :=
  let ⟨K, M, hK_nn, hM_pos, _⟩ := hls_substantive_bound hf hβJd_pos hβJd_lt
  ⟨K, M, hK_nn, hM_pos⟩

end Ambient
end IsingModel
