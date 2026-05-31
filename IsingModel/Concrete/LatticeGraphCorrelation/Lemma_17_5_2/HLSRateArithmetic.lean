import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSNonnegWitnesses

/-!
# Substantive HLS rate arithmetic bundle

GJ-proposition-unit bundle providing arithmetic identities and bounds on
the high-temperature decay rate `M = -log(β·J·(2d))`.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Rate arithmetic -/

/-- **Rate ne zero**: `-log(β·J·(2d)) ≠ 0`. -/
theorem hls_log_rate_ne_zero
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    -Real.log (β * J * ↑(2 * d)) ≠ 0 :=
  (hls_log_rate_pos hd hβJ hβJd_lt).ne'

/-- **Rate squared positivity**: `(-log(β·J·(2d)))^2 > 0`. -/
theorem hls_log_rate_sq_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 < (-Real.log (β * J * ↑(2 * d))) ^ 2 :=
  pow_pos (hls_log_rate_pos hd hβJ hβJd_lt) 2

/-- **Rate squared nonneg**. -/
theorem hls_log_rate_sq_nonneg
    {d : ℕ} {β J : ℝ} :
    0 ≤ (-Real.log (β * J * ↑(2 * d))) ^ 2 :=
  sq_nonneg _

/-- **Rate halved positive**: `(-log(β·J·(2d)))/2 > 0`. -/
theorem hls_log_rate_half_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 < (-Real.log (β * J * ↑(2 * d))) / 2 :=
  div_pos (hls_log_rate_pos hd hβJ hβJd_lt) (by norm_num)

/-- **Rate doubled positive**: `2 · (-log(β·J·(2d))) > 0`. -/
theorem hls_log_rate_two_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 < 2 * (-Real.log (β * J * ↑(2 * d))) :=
  mul_pos (by norm_num) (hls_log_rate_pos hd hβJ hβJd_lt)

/-- **Rate sum of squares**: `2 · M^2 > 0`. -/
theorem hls_log_rate_two_sq_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 < 2 * (-Real.log (β * J * ↑(2 * d))) ^ 2 :=
  mul_pos (by norm_num) (hls_log_rate_sq_pos hd hβJ hβJd_lt)

end Ambient
end IsingModel
