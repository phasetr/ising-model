import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSSubstantiveBundle
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation

/-!
# Substantive HLS → cluster property bundle

GJ-proposition-unit bundle linking the substantive HLS bundle (#3199):
- `hasExponentialDecay_of_simonLieb_ferromagnetic_high_temp`

to the cluster property via the existing
`clusterProperty_latticeGraph_of_HasExponentialDecay` consumer.

**Reference:** Glimm-Jaffe §17.5 / §5.1.
-/

namespace IsingModel
namespace Ambient

/-! ## clusterProperty from substantive Simon-Lieb HasExponentialDecay -/

/-- **`clusterProperty` from Simon-Lieb ferromagnetic high-temp** (substantive
chain: Step 5.7h → HasExponentialDecay → clusterProperty). -/
theorem clusterProperty_latticeGraph_of_simonLieb_ferromagnetic_high_temp
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) := by
  have hSL_pos : 0 < simonLiebRate β J d := simonLiebRate_pos hβJd_pos hβJd_lt
  have hSL_half_pos : 0 < simonLiebRate β J d / 2 := by linarith
  have h_decay := hasExponentialDecay_of_simonLieb_ferromagnetic_high_temp
    hf hβJd_pos hβJd_lt.le
  exact clusterProperty_latticeGraph_of_HasExponentialDecay d
    (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hSL_half_pos
    h_decay

/-! ## Per-site cofinite tendsto from substantive Simon-Lieb -/

/-- **Per-site cofinite tendsto of truncated2Infinite to 0** under
ferromagnetic high-temp via Simon-Lieb. -/
theorem truncated2Infinite_tendsto_cofinite_zero_of_simonLieb_ferromagnetic_high_temp
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1)
    (i : Fin d → ℤ) :
    Filter.Tendsto (fun j : Fin d → ℤ =>
        truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) i j) Filter.cofinite (nhds 0) :=
  clusterProperty_latticeGraph_of_simonLieb_ferromagnetic_high_temp
    hf hβJd_pos hβJd_lt i

/-! ## Correlation-form cluster -/

/-- **Per-site cofinite tendsto of correlationInfinite to 0** at `h = 0`. -/
theorem correlationInfinite_tendsto_cofinite_zero_of_simonLieb_ferromagnetic_high_temp
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1)
    (i : Fin d → ℤ) :
    Filter.Tendsto (fun j : Fin d → ℤ =>
        correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}) Filter.cofinite (nhds 0) := by
  have h_t2 := truncated2Infinite_tendsto_cofinite_zero_of_simonLieb_ferromagnetic_high_temp
    hf hβJd_pos hβJd_lt i
  have h_eq : (fun j : Fin d → ℤ =>
      truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) i j) =
      (fun j : Fin d → ℤ =>
        correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}) := by
    funext j
    exact truncated2Infinite_latticeGraph_h_zero d J β i j
  rw [h_eq] at h_t2
  exact h_t2

/-! ## HasExponentialDecay rate accessors -/

/-- **Explicit decay rate `simonLiebRate β J d / 2` accessor**. -/
theorem hasExponentialDecay_simonLiebRate_half_of_ferromagnetic_high_temp
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1) :
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (simonLiebRate β J d / 2) :=
  hasExponentialDecay_of_simonLieb_ferromagnetic_high_temp
    hf hβJd_pos hβJd_lt.le

/-- **Decay rate positivity helper**. -/
theorem hasExponentialDecay_rate_pos_of_ferromagnetic_strict_high_temp
    {β J : ℝ} {d : ℕ}
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1) :
    0 < simonLiebRate β J d / 2 := by
  have hSL_pos : 0 < simonLiebRate β J d := simonLiebRate_pos hβJd_pos hβJd_lt
  linarith

/-! ## Bundle witness existential -/

/-- **Existence of a positive decay rate for `Ferromagnetic` + strict high-temp**. -/
theorem exists_pos_rate_hasExponentialDecay_of_simonLieb_ferromagnetic_high_temp
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1) :
    ∃ α : ℝ, 0 < α ∧
      HasExponentialDecay d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) α :=
  ⟨simonLiebRate β J d / 2,
    hasExponentialDecay_rate_pos_of_ferromagnetic_strict_high_temp hβJd_pos hβJd_lt,
    hasExponentialDecay_simonLiebRate_half_of_ferromagnetic_high_temp
      hf hβJd_pos hβJd_lt⟩

end Ambient
end IsingModel
