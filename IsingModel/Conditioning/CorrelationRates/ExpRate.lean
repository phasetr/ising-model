import IsingModel.Conditioning.CorrelationClosed.PairBound

/-!
# Correlation rates split — high-temperature exponential rate and exp-rate distance bounds

Part of the split high-temperature correlation-rates layer (Issue #1850).
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Ferromagnetic §18.7 capstone**: under `0 ≤ J, 0 < β`,
\[
\langle \sigma_i \sigma_j \rangle_{\beta, 0}
  \le 2^{|E|} \cdot \tanh(\beta J)^{d_G(i,j)}.
\]
Bridges ferromagnetic hypotheses with the abstract capstone via
`mul_nonneg hβ.le hJ`. -/
theorem
correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι)
      ≤ (2 : ℝ) ^ G.edgeFinset.card * Real.tanh (β * J) ^ G.dist i j :=
  correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    G J β (mul_nonneg hβ.le hJ) i j

/-- **Named high-temperature §18.7 rate**:
`highTempExpRate β J = -log(tanh(β J))`. This is the rate used by the
exponential form of the finite-volume high-temperature pair-correlation
decay bound. Lean's total `Real.log 0 = 0` makes the zero-activity
endpoint rate equal to `0`. -/
noncomputable def highTempExpRate (β J : ℝ) : ℝ :=
  -Real.log (Real.tanh (β * J))

@[simp] theorem highTempExpRate_at_beta_zero (J : ℝ) :
    highTempExpRate 0 J = 0 := by
  simp [highTempExpRate]

@[simp] theorem highTempExpRate_at_J_zero (β : ℝ) :
    highTempExpRate β 0 = 0 := by
  simp [highTempExpRate]

/-- The named high-temperature rate is nonnegative when `0 ≤ β·J`. -/
theorem highTempExpRate_nonneg {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 ≤ highTempExpRate β J := by
  unfold highTempExpRate
  have htanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  exact neg_nonneg.mpr (Real.log_nonpos htanh_nn (Real.tanh_lt_one _).le)

/-- Ferromagnetic bridge for `highTempExpRate_nonneg`. -/
theorem highTempExpRate_ferromagnetic_nonneg {β J : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    0 ≤ highTempExpRate β J :=
  highTempExpRate_nonneg (mul_nonneg hβ.le hJ)

/-- **Rate-form §18.7 capstone**: the finite-volume high-temperature
pair-correlation distance bound can be written with the explicit rate
`-log(tanh(β J))`. Under `0 ≤ β * J`,
\[
\langle \sigma_i \sigma_j \rangle_{\beta,0}
  \le 2^{|E|} \exp\{-(-\log(\tanh(\beta J)))\,d_G(i,j)\}.
\]
When `tanh(β J)=0`, Lean's total `Real.log 0 = 0` makes the right-hand
side `2^{|E|}`, so the statement remains a valid endpoint form of the
tanh-power capstone. -/
theorem correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι)
      ≤ (2 : ℝ) ^ G.edgeFinset.card *
        Real.exp (-(-Real.log (Real.tanh (β * J))) * (G.dist i j : ℝ)) := by
  have hbase :=
    correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
      G J β hβJ i j
  have htanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  have htanh_le_one : Real.tanh (β * J) ≤ 1 := (Real.tanh_lt_one _).le
  have hpow_le_exp : Real.tanh (β * J) ^ G.dist i j
      ≤ Real.exp (-(-Real.log (Real.tanh (β * J))) * (G.dist i j : ℝ)) := by
    by_cases hzero : Real.tanh (β * J) = 0
    · rw [hzero, Real.log_zero, neg_zero, neg_zero, zero_mul, Real.exp_zero]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    · have htanh_pos : 0 < Real.tanh (β * J) :=
        lt_of_le_of_ne htanh_nn (Ne.symm hzero)
      have hpow_exp : Real.tanh (β * J) ^ G.dist i j =
          Real.exp (-(-Real.log (Real.tanh (β * J))) * (G.dist i j : ℝ)) := by
        rw [← Real.exp_log (pow_pos htanh_pos (G.dist i j)), Real.log_pow]
        ring_nf
      exact le_of_eq hpow_exp
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hpow_le_exp (pow_nonneg (by norm_num) _))

/-- **Named-rate §18.7 capstone**: the rate-form pair-correlation bound
using `highTempExpRate`. -/
theorem correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι)
      ≤ (2 : ℝ) ^ G.edgeFinset.card *
        Real.exp (-(highTempExpRate β J) * (G.dist i j : ℝ)) := by
  simpa [highTempExpRate] using
    correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
      G J β hβJ i j

/-- Ferromagnetic bridge for the named-rate §18.7 capstone. -/
theorem
correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι)
      ≤ (2 : ℝ) ^ G.edgeFinset.card *
        Real.exp (-(highTempExpRate β J) * (G.dist i j : ℝ)) :=
  correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist
    G J β (mul_nonneg hβ.le hJ) i j

/-- **Ferromagnetic rate-form §18.7 capstone**: under `0 ≤ J, 0 < β`,
the finite-volume pair correlation is bounded by
`2^|E| * exp(-(-log(tanh(β J))) * dist)`. -/
theorem
correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι)
      ≤ (2 : ℝ) ^ G.edgeFinset.card *
        Real.exp (-(-Real.log (Real.tanh (β * J))) * (G.dist i j : ℝ)) :=
  correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    G J β (mul_nonneg hβ.le hJ) i j

/-- **Monotone-rate §18.7 capstone**: any real rate `α` no larger than
the explicit high-temperature rate `-log(tanh(β J))` may replace the
exact rate in the finite-volume pair-correlation bound. This is a
consumer-facing weakening of
`correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist`. -/
theorem correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β α : ℝ) (hβJ : 0 ≤ β * J)
    (hα : α ≤ -Real.log (Real.tanh (β * J))) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι)
      ≤ (2 : ℝ) ^ G.edgeFinset.card * Real.exp (-α * (G.dist i j : ℝ)) := by
  have hbase :=
    correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
      G J β hβJ i j
  have hdist_nn : 0 ≤ (G.dist i j : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have h_exp_le :
      Real.exp (-(-Real.log (Real.tanh (β * J))) * (G.dist i j : ℝ)) ≤
        Real.exp (-α * (G.dist i j : ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg hα) hdist_nn
  exact hbase.trans
    (mul_le_mul_of_nonneg_left h_exp_le (pow_nonneg (by norm_num) _))

/-- **Named monotone-rate §18.7 capstone**: any `α ≤ highTempExpRate β J`
may replace the named high-temperature rate in the finite-volume
pair-correlation bound. -/
theorem
correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist_of_le_highTempExpRate
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β α : ℝ) (hβJ : 0 ≤ β * J)
    (hα : α ≤ highTempExpRate β J) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι)
      ≤ (2 : ℝ) ^ G.edgeFinset.card * Real.exp (-α * (G.dist i j : ℝ)) := by
  simpa [highTempExpRate] using
    correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
      G J β α hβJ hα i j

/-- Ferromagnetic bridge for the named monotone-rate §18.7 capstone. -/
theorem
correlation_high_temp_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β α : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (hα : α ≤ highTempExpRate β J) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι)
      ≤ (2 : ℝ) ^ G.edgeFinset.card * Real.exp (-α * (G.dist i j : ℝ)) :=
  correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist_of_le_highTempExpRate
    G J β α (mul_nonneg hβ.le hJ) hα i j

/-- **Ferromagnetic monotone-rate §18.7 capstone**: under
`0 ≤ J, 0 < β`, any `α ≤ -log(tanh(β J))` gives the finite-volume
bound with rate `α`. -/
theorem
correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β α : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (hα : α ≤ -Real.log (Real.tanh (β * J))) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι)
      ≤ (2 : ℝ) ^ G.edgeFinset.card * Real.exp (-α * (G.dist i j : ℝ)) :=
  correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    G J β α (mul_nonneg hβ.le hJ) hα i j


/-! ## Step 119 plan Step 5.7d: `tanh^d ≤ exp(-(M·d·r))` bridge -/

/-- **`tanh(β·J)^d ≤ exp(-(M·d·r))`** when `M·r ≤ highTempExpRate β J`,
under `0 ≤ β·J` (Step 119 plan Step 5.7d).

Direct calculation: when `tanh(β·J) > 0`,
`tanh(β·J)^d = exp(d · log(tanh(β·J))) = exp(-(highTempExpRate β J) · d)`.
Since `M·r ≤ highTempExpRate β J`, multiplying by the nonneg distance
`d` gives `M·r·d ≤ highTempExpRate·d`, hence
`-highTempExpRate·d ≤ -(M·r·d)`, hence
`exp(-highTempExpRate·d) ≤ exp(-(M·r·d)) = exp(-(M·d·r))`.

The zero-`tanh(β·J)` endpoint splits by `d`: for `d = 0` we have
`tanh(β·J)^0 = 1 = exp(0)`; for `d > 0` we have `tanh(β·J)^d = 0 ≤ exp(...)`.

This is the analytic bridge from cubic-path tanh decay
`correlation ≤ tanh(β·J)^d` into `correlation ≤ exp(-(M·d·r))`, which
combined with `pseudoMassG_ge_exp_of_tr_le_one` (small-`t·r` regime,
`PseudoMass/Profile.lean`) and the bound reduction of #3173 lands the
analytic input directly in the `bridge.bound` shape
`M·d ≤ pseudoMass·r`. -/
theorem tanh_pow_le_exp_neg_M_dist_r_of_M_r_le_highTempExpRate
    {β J : ℝ} (hβJ : 0 ≤ β * J) {M r : ℝ}
    (hMr : M * r ≤ highTempExpRate β J) (d : ℕ) :
    Real.tanh (β * J) ^ d ≤ Real.exp (-(M * (d : ℝ) * r)) := by
  have htanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  by_cases hzero : Real.tanh (β * J) = 0
  · rw [hzero]
    have hd : (0 : ℝ) ≤ Real.exp (-(M * (d : ℝ) * r)) := (Real.exp_pos _).le
    rcases Nat.eq_zero_or_pos d with hd0 | hd_pos
    · rw [hd0, pow_zero]
      have h0 : 0 ≤ M * (0 : ℝ) * r := by
        rw [mul_zero, zero_mul]
      have : -(M * (0 : ℝ) * r) = 0 := by simp
      rw [Nat.cast_zero] at *
      simp [Real.exp_zero]
    · rw [zero_pow (Nat.pos_iff_ne_zero.mp hd_pos)]
      exact hd
  · have htanh_pos : 0 < Real.tanh (β * J) :=
      lt_of_le_of_ne htanh_nn (Ne.symm hzero)
    have hpow_eq : Real.tanh (β * J) ^ d =
        Real.exp (-(highTempExpRate β J) * (d : ℝ)) := by
      rw [← Real.exp_log (pow_pos htanh_pos d), Real.log_pow]
      unfold highTempExpRate
      ring_nf
    rw [hpow_eq]
    apply Real.exp_le_exp.mpr
    have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le _
    have hMr_d : M * r * (d : ℝ) ≤ highTempExpRate β J * (d : ℝ) :=
      mul_le_mul_of_nonneg_right hMr hd_nn
    nlinarith

end IsingModel
