import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSExistingExtensions
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation

/-!
# Existing-rate HasExponentialDecay → cluster property + tendsto bundle

GJ-proposition-unit bundle: existing-rate (`-log(β·J·(2d))`)
HasExponentialDecay → cluster property and per-site cofinite tendsto
ferromagnetic-form aliases.

Mirror structure of #3201 (which was for the half-rate #3199 version)
adapted to the STRONGER full-rate version.

**Reference:** Glimm-Jaffe §17.5 / §5.1.
-/

namespace IsingModel
namespace Ambient

/-! ## clusterProperty from existing-rate HasExponentialDecay -/

/-- **`clusterProperty` from existing high-temp HasExponentialDecay**
(ferromagnetic + strict high-temp). -/
theorem clusterProperty_latticeGraph_of_existing_ferromagnetic_high_temp
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) := by
  have hα_pos := neg_log_betaJ_two_d_pos_of_strict_high_temp hβJd_pos hβJd_lt
  have h_decay := hasExponentialDecay_of_high_temp
    (mul_nonneg hf.hβ.le hf.hJ) hβJd_lt
  exact clusterProperty_latticeGraph_of_HasExponentialDecay d
    (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hα_pos h_decay

/-! ## Per-site cofinite tendsto -/

/-- **Per-site cofinite tendsto of truncated2Infinite to 0** under
ferromagnetic high-temp via existing HasExponentialDecay. -/
theorem truncated2Infinite_tendsto_cofinite_zero_of_existing_ferromagnetic_high_temp
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    Filter.Tendsto (fun j : Fin d → ℤ =>
        truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) i j) Filter.cofinite (nhds 0) :=
  clusterProperty_latticeGraph_of_existing_ferromagnetic_high_temp
    hf hβJd_pos hβJd_lt i

/-- **Per-site cofinite tendsto of correlationInfinite to 0** at `h = 0`
via existing HasExponentialDecay. -/
theorem correlationInfinite_tendsto_cofinite_zero_of_existing_ferromagnetic_high_temp
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    Filter.Tendsto (fun j : Fin d → ℤ =>
        correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}) Filter.cofinite (nhds 0) := by
  have h_t2 :=
    truncated2Infinite_tendsto_cofinite_zero_of_existing_ferromagnetic_high_temp
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

/-! ## HasExponentialDecay rate accessors (existing rate) -/

/-- **Explicit decay rate `-log(β·J·(2d))` accessor** (existing
ferromagnetic high-temp). -/
theorem hasExponentialDecay_existing_rate_of_ferromagnetic_high_temp
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * ↑(2 * d))) :=
  hasExponentialDecay_of_high_temp (mul_nonneg hf.hβ.le hf.hJ) hβJd_lt

/-- **Existence of a positive decay rate via existing HasExponentialDecay**. -/
theorem exists_pos_rate_hasExponentialDecay_of_existing_ferromagnetic_high_temp
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ α : ℝ, 0 < α ∧
      HasExponentialDecay d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) α :=
  ⟨-Real.log (β * J * ↑(2 * d)),
    neg_log_betaJ_two_d_pos_of_strict_high_temp hβJd_pos hβJd_lt,
    hasExponentialDecay_existing_rate_of_ferromagnetic_high_temp hf hβJd_lt⟩

end Ambient
end IsingModel
