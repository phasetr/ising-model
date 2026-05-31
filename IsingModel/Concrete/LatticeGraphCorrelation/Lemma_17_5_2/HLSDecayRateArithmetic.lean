import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSRateArithmetic

/-!
# Substantive HLS decay rate arithmetic bundle (additional)

GJ-proposition-unit bundle providing additional arithmetic identities
on the decay rate.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Additional rate identities -/

/-- **Rate cubed positivity**. -/
theorem hls_log_rate_cube_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 < (-Real.log (β * J * ↑(2 * d))) ^ 3 :=
  pow_pos (hls_log_rate_pos hd hβJ hβJd_lt) 3

/-- **Rate to power n positivity** for n ≥ 0. -/
theorem hls_log_rate_pow_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (n : ℕ) :
    0 < (-Real.log (β * J * ↑(2 * d))) ^ n :=
  pow_pos (hls_log_rate_pos hd hβJ hβJd_lt) n

/-- **Rate to power n nonneg**. -/
theorem hls_log_rate_pow_nonneg
    {d : ℕ} {β J : ℝ} (n : ℕ) :
    0 ≤ (-Real.log (β * J * ↑(2 * d))) ^ n ∨
    n % 2 = 1 := by
  rcases Nat.even_or_odd n with heven | hodd
  · left
    exact Even.pow_nonneg heven _
  · right
    rcases hodd with ⟨k, hk⟩
    omega

/-- **Rate × n > 0** for `n ≥ 1`. -/
theorem hls_log_rate_n_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    0 < (n : ℝ) * (-Real.log (β * J * ↑(2 * d))) := by
  apply mul_pos
  · exact_mod_cast hn
  · exact hls_log_rate_pos hd hβJ hβJd_lt

/-- **Rate × n nonneg** for any `n`. -/
theorem hls_log_rate_n_nonneg
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (n : ℕ) :
    0 ≤ (n : ℝ) * (-Real.log (β * J * ↑(2 * d))) := by
  apply mul_nonneg
  · exact_mod_cast Nat.zero_le n
  · exact (hls_log_rate_pos hd hβJ hβJd_lt).le

/-- **Rate + ε > 0** for ε ≥ 0. -/
theorem hls_log_rate_plus_eps_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    0 < -Real.log (β * J * ↑(2 * d)) + ε :=
  add_pos_of_pos_of_nonneg (hls_log_rate_pos hd hβJ hβJd_lt) hε

end Ambient
end IsingModel
