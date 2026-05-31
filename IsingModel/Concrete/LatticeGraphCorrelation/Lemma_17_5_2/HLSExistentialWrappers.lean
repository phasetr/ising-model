import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSConjunction

/-!
# Substantive HLS existential wrappers bundle

GJ-proposition-unit bundle exposing existential forms of substantive HLS
conclusions.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Existential wrappers -/

/-- **Existential HasExponentialDecay**. -/
theorem hls_exists_hasExpDecay
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ α : ℝ, HasExponentialDecay d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) α :=
  ⟨_, hls_hasExpDecay hd hf hβJ hβJd_lt⟩

/-- **Existential positive `α` with HasExponentialDecay**. -/
theorem hls_exists_alpha_pos_hasExpDecay
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ α : ℝ, 0 < α ∧ HasExponentialDecay d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) α := by
  have hd_pos : 0 < d := hd
  have h2d_pos : (0 : ℝ) < 2 * d := by positivity
  have hβJd_pos : 0 < β * J * (2 * d) := mul_pos hβJ h2d_pos
  refine ⟨-Real.log (β * J * ↑(2 * d)),
          neg_log_betaJ_two_d_pos_of_strict_high_temp hβJd_pos hβJd_lt,
          ?_⟩
  exact hls_hasExpDecay hd hf hβJ hβJd_lt

/-- **Existential bounded susceptibility**. -/
theorem hls_exists_susceptibility_bound
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ i : Fin d → ℤ,
        susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
          ≤ B := by
  refine ⟨β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)), ?_, ?_⟩
  · have h_denom_pos : (0 : ℝ) < 1 - β * J * ↑(2 * d) := by linarith
    have h_numer_nn : (0 : ℝ) ≤ β * J * ↑(2 * d) :=
      mul_nonneg (mul_nonneg hf.hβ.le hf.hJ) (by positivity)
    exact div_nonneg h_numer_nn h_denom_pos.le
  · intro i
    exact hls_susc hd hf hβJ hβJd_lt i

/-- **Existential positive latticeMass**. -/
theorem hls_exists_latticeMass_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ m : ENNReal, 0 < m ∧
      m = latticeMass d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) :=
  ⟨_, hls_latticeMass hd hf hβJ hβJd_lt, rfl⟩

/-- **Existential clusterProperty**. -/
theorem hls_exists_clusterProperty
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ _h : clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ), True :=
  ⟨hls_cluster hd hf hβJ hβJd_lt, trivial⟩

end Ambient
end IsingModel
