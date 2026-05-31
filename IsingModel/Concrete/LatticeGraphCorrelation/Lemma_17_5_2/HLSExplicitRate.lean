import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSIffCharacterizations

/-!
# Substantive HLS explicit rate bundle

GJ-proposition-unit bundle exposing the explicit decay rate
`-log(β·J·(2d))` as the canonical HLS rate.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Explicit rate wrappers -/

/-- **`-log(β·J·(2d)) > 0` from strict high-temp**. -/
theorem hls_explicit_rate_pos
    {β J : ℝ} {d : ℕ}
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 : ℝ) < -Real.log (β * J * ↑(2 * d)) :=
  neg_log_betaJ_two_d_pos_of_strict_high_temp hβJd_pos hβJd_lt

/-- **Canonical rate name: `hls_canonical_decay_rate`**. -/
noncomputable def hls_canonical_decay_rate (β J : ℝ) (d : ℕ) : ℝ :=
  -Real.log (β * J * ↑(2 * d))

/-- **Canonical decay rate equals `-log(β·J·(2d))`** by definition. -/
theorem hls_canonical_decay_rate_eq
    (β J : ℝ) (d : ℕ) :
    hls_canonical_decay_rate β J d = -Real.log (β * J * ↑(2 * d)) :=
  rfl

/-- **Canonical decay rate is positive under strict high-temp**. -/
theorem hls_canonical_decay_rate_pos
    {β J : ℝ} {d : ℕ}
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 : ℝ) < hls_canonical_decay_rate β J d :=
  hls_explicit_rate_pos hβJd_pos hβJd_lt

/-- **HasExponentialDecay at canonical decay rate**. -/
theorem hls_hasExpDecay_canonical
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (hls_canonical_decay_rate β J d) :=
  hls_hasExpDecay hd hf hβJ hβJd_lt

/-- **Existential positive rate via canonical decay rate**. -/
theorem hls_exists_pos_rate_canonical
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ α : ℝ, 0 < α ∧
      HasExponentialDecay d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) α := by
  have hd_pos : 0 < d := hd
  have h2d_pos : (0 : ℝ) < 2 * d := by positivity
  have hβJd_pos : 0 < β * J * (2 * d) := mul_pos hβJ h2d_pos
  refine ⟨hls_canonical_decay_rate β J d,
          hls_canonical_decay_rate_pos hβJd_pos hβJd_lt, ?_⟩
  exact hls_hasExpDecay_canonical hd hf hβJ hβJd_lt

end Ambient
end IsingModel
