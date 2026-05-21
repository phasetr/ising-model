import IsingModel.Conditioning.CorrelationClosed

/-!
# Correlation Rates

This module is part of the split `IsingModel.Conditioning` development.
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

/-- **Pair correlation weak upper bound `≤ 2^|E| · tanh(β·J)` at `h = 0`
(GJ §18.7 weak upper bound)**: under `0 ≤ β·J`,
\[
\langle \sigma_i \sigma_j \rangle_{\beta, 0}
  \le 2^{|E|} \cdot \tanh(\beta J).
\]

A weak quantitative version of GJ §18.7 / FV §3.7.3 — *not* yet
exponential decay in graph distance, but the natural companion to the
single-edge tanh **lower** bound `tanh / 2^|E| ≤ ⟨σ_iσ_j⟩` (Step 386).

Proof:
1. Step 566 reduces to numerator-only: `correlation ≤ N`.
2. Each contributing `X` has `1 ≤ |X|` (Step 567), so
   `tanh(β·J)^|X| ≤ tanh(β·J)^1 = tanh(β·J)` since
   `0 ≤ tanh(β·J) ≤ 1` (`Real.tanh_lt_one`).
3. `N ≤ |filter| · tanh(β·J) ≤ 2^|E| · tanh(β·J)` since the filter is
   a subset of `G.edgeFinset.powerset` whose cardinality is `2^|E|`.

References: GJ §18.7; FV §3.7.3 eq. (3.46), p. 117 (2017 ed.). -/
theorem correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι)
      ≤ (2 : ℝ) ^ G.edgeFinset.card * Real.tanh (β * J) := by
  classical
  have htanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg
      (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  have htanh_le_one : Real.tanh (β * J) ≤ 1 := (Real.tanh_lt_one _).le
  -- Step 566: correlation ≤ N
  have h_step1 := correlation_high_temp_h_zero_le_numerator
    G J β hβJ ({i, j} : Finset ι)
  -- Step 2: each X in numerator filter satisfies |X| ≥ 1, so tanh^|X| ≤ tanh
  set F : Finset (Finset (Sym2 ι)) :=
    G.edgeFinset.powerset.filter (fun X : Finset (Sym2 ι) => ∀ v : ι,
      Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
            + (X.filter (v ∈ ·)).card)) with hF_def
  have h_term_le : ∀ X ∈ F, Real.tanh (β * J) ^ X.card ≤ Real.tanh (β * J) := by
    intro X hX
    have hX_card_pos : 1 ≤ X.card :=
      evenSubgraph_pair_boundary_card_pos G i j X hX
    have h_pow_le : Real.tanh (β * J) ^ X.card ≤ Real.tanh (β * J) ^ 1 :=
      pow_le_pow_of_le_one htanh_nn htanh_le_one hX_card_pos
    rwa [pow_one] at h_pow_le
  -- Step 3: ∑ over F of tanh^|X| ≤ |F| · tanh ≤ 2^|E| · tanh
  have h_sum_le_card_smul : (∑ X ∈ F, Real.tanh (β * J) ^ X.card)
      ≤ F.card • Real.tanh (β * J) :=
    Finset.sum_le_card_nsmul F _ _ h_term_le
  -- |F| ≤ |powerset| = 2^|E|
  have h_F_subset : F ⊆ G.edgeFinset.powerset := Finset.filter_subset _ _
  have h_F_card_le : F.card ≤ G.edgeFinset.powerset.card :=
    Finset.card_le_card h_F_subset
  have h_powerset_card : G.edgeFinset.powerset.card = 2 ^ G.edgeFinset.card :=
    Finset.card_powerset _
  have h_F_card_le_two_pow : F.card ≤ 2 ^ G.edgeFinset.card := by
    rw [← h_powerset_card]; exact h_F_card_le
  -- Convert nsmul to mul
  have h_smul_eq : F.card • Real.tanh (β * J) =
      (F.card : ℝ) * Real.tanh (β * J) := by
    rw [nsmul_eq_mul]
  rw [h_smul_eq] at h_sum_le_card_smul
  have h_smul_le : (F.card : ℝ) * Real.tanh (β * J)
      ≤ (2 : ℝ) ^ G.edgeFinset.card * Real.tanh (β * J) := by
    apply mul_le_mul_of_nonneg_right _ htanh_nn
    exact_mod_cast h_F_card_le_two_pow
  -- Combine
  exact h_step1.trans (h_sum_le_card_smul.trans h_smul_le)

/-- **Z₂ symmetry of correlations at h = 0 from FV (3.46) + handshake**:
for any `A : Finset ι` of odd cardinality, `correlation G ⟨J, 0, β⟩ A = 0`.

A direct combinatorial proof going through:
1. `correlation_high_temp_expansion_h_zero_closed` (FV (3.46), Step 284)
2. `high_temp_numerator_filter_eq_empty_of_odd_card` (Step 297) — the
   numerator filter is *literally empty* by edge-vertex handshake.
3. `Finset.sum_empty`: empty sum is `0`; `0 / x = 0`.

Independent of `correlation_odd_vanish` (the standard spin-flip Z₂
argument). Provides a fully closed-form / combinatorial alternative. -/
theorem correlation_high_temp_h_zero_odd_card_eq_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) (hA_odd : Odd A.card) :
    correlation G ⟨J, 0, β⟩ A = 0 := by
  rw [correlation_high_temp_expansion_h_zero_closed,
      high_temp_numerator_filter_eq_empty_of_odd_card G A hA_odd,
      Finset.sum_empty, zero_div]

/-- **Pair correlation nonnegativity at h = 0 from FV (3.46)**: under
`0 ≤ β·J`, `0 ≤ ⟨σ_i σ_j⟩_{β,0}` for any `i, j : ι`.
Direct specialization of `correlation_high_temp_h_zero_nonneg` (Step 293)
at A = {i, j}. -/
theorem correlation_high_temp_h_zero_at_pair_nonneg
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ι) :
    0 ≤ correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) :=
  correlation_high_temp_h_zero_nonneg G J β hβJ {i, j}

/-- **Pair correlation ≤ 1 at h = 0**: `⟨σ_i σ_j⟩_{β,0} ≤ 1`.
Specialization of the general `correlation_le_one`. -/
theorem correlation_high_temp_h_zero_at_pair_le_one
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ≤ 1 :=
  correlation_le_one G ⟨J, 0, β⟩ {i, j}

/-- **Pair correlation sandwich at h = 0**: under `0 ≤ β·J`,
`0 ≤ ⟨σ_i σ_j⟩_{β,0} ≤ 1`. Combines Steps 340 and 341. -/
theorem correlation_high_temp_h_zero_at_pair_sandwich
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ι) :
    0 ≤ correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ∧
      correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ≤ 1 :=
  ⟨correlation_high_temp_h_zero_at_pair_nonneg G J β hβJ i j,
   correlation_high_temp_h_zero_at_pair_le_one G J β i j⟩

/-- **Pair correlation at J = 0, h = 0 vanishes**: at `J = 0, h = 0`,
`⟨σ_i σ_j⟩ = 0` for any `i, j : ι`. Direct from `correlation_J_zero`
which gives `⟨σ_A⟩ = tanh(β · h)^|A|`; at `h = 0` and `A = {i, j}`
(nonempty), this gives `0`. -/
theorem correlation_high_temp_h_zero_at_pair_J_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) (i j : ι) :
    correlation G ⟨0, 0, β⟩ ({i, j} : Finset ι) = 0 := by
  classical
  rw [correlation_J_zero, mul_zero, Real.tanh_zero]
  have hcard_pos : 0 < ({i, j} : Finset ι).card := by
    rw [Finset.card_pos]; exact ⟨i, by simp⟩
  exact zero_pow hcard_pos.ne'

/-- **Pair correlation at β = 0, h = 0 vanishes**: at `β = 0, h = 0`,
`⟨σ_i σ_j⟩ = 0` for any `i, j : ι`. Direct from
`correlation_beta_zero_vanish_of_nonempty_A`. -/
theorem correlation_high_temp_h_zero_at_pair_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) (i j : ι) :
    correlation G ⟨J, 0, 0⟩ ({i, j} : Finset ι) = 0 := by
  refine correlation_beta_zero_vanish_of_nonempty_A G J 0 {i, j} ?_
  exact ⟨i, by simp⟩

/-- **Singleton magnetization at J = 0, h = 0 vanishes**: at `J = 0, h = 0`,
`⟨σ_i⟩ = 0`. -/
theorem correlation_high_temp_h_zero_at_singleton_J_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) (i : ι) :
    correlation G ⟨0, 0, β⟩ ({i} : Finset ι) = 0 := by
  classical
  rw [correlation_J_zero, mul_zero, Real.tanh_zero, Finset.card_singleton,
      pow_one]

/-- **Singleton magnetization at β = 0, h = 0 vanishes**: at `β = 0, h = 0`,
`⟨σ_i⟩ = 0`. -/
theorem correlation_high_temp_h_zero_at_singleton_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) (i : ι) :
    correlation G ⟨J, 0, 0⟩ ({i} : Finset ι) = 0 :=
  correlation_beta_zero_vanish_of_nonempty_A G J 0 {i} ⟨i, by simp⟩

/-- **Singleton magnetization absolute bound at h = 0 from FV (3.46)**:
`|⟨σ_i⟩_{β,0}| ≤ 1`. Combined with Step 331 (`⟨σ_i⟩ = 0`), this is
trivially `0 ≤ 1` but useful as a conventional restatement. -/
theorem correlation_high_temp_h_zero_at_singleton_abs_le_one
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i : ι) :
    |correlation G ⟨J, 0, β⟩ ({i} : Finset ι)| ≤ 1 :=
  abs_correlation_le_one G ⟨J, 0, β⟩ {i}

/-- **Z complete-summary bundle at h = 0**: under `0 ≤ β·J`, single
statement bundling all known §18.3 properties of `Z` at `h = 0`:
  1. `2^|ι| · cosh(βJ)^|E| ≤ Z` (lower bound from FV (3.45)),
  2. `Z ≤ 2^(|ι|+|E|) · cosh(βJ)^|E|` (upper bound from FV (3.45)),
  3. `Z⟨0, 0, β⟩ = 2^|ι|` (consistency at trivial slice `J = 0`),
  4. `Z⟨J, 0, 0⟩ = 2^|ι|` (consistency at trivial slice `β = 0`).
Useful as a single import for downstream analytic / asymptotic
arguments that need both bounds and trivial-slice values. -/
theorem partitionFunction_high_temp_expansion_h_zero_complete_summary
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card
        ≤ partitionFunction G ⟨J, 0, β⟩ ∧
      partitionFunction G ⟨J, 0, β⟩
        ≤ (2 : ℝ) ^ (Fintype.card ι + G.edgeFinset.card) *
            Real.cosh (β * J) ^ G.edgeFinset.card ∧
      partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
        = (2 : ℝ) ^ Fintype.card ι ∧
      partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
        = (2 : ℝ) ^ Fintype.card ι :=
  ⟨partitionFunction_high_temp_expansion_h_zero_lower_bound G J β hβJ,
   partitionFunction_high_temp_expansion_h_zero_upper_bound G J β hβJ,
   partitionFunction_high_temp_expansion_h_zero_closed_at_J_zero G β,
   partitionFunction_high_temp_expansion_h_zero_closed_at_beta_zero G J⟩

/-- **freeEnergy complete-summary bundle at h = 0**: under `0 < |ι|` and
`0 ≤ β·J`, single statement bundling all known §18.3 properties of
`f` at `h = 0`:
  1. `log 2 + (|E|/|ι|) log cosh(βJ) ≤ f` (lower bound),
  2. `f ≤ log 2 + (|E|/|ι|) log(2·cosh(βJ))` (upper bound),
  3. `f⟨0, 0, β⟩ = log 2` (consistency at trivial slice `J = 0`,
     specialisation of `freeEnergy_J_zero` at `h = 0`),
  4. `f⟨J, 0, 0⟩ = log 2` (consistency at trivial slice `β = 0`).
Useful as a single import for downstream analytic / asymptotic
arguments that need both bounds and trivial-slice values. -/
theorem freeEnergy_high_temp_h_zero_complete_summary
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
      ≤ freeEnergy G ⟨J, 0, β⟩ ∧
      freeEnergy G ⟨J, 0, β⟩
        ≤ Real.log 2 + (G.edgeFinset.card : ℝ) / Fintype.card ι *
            Real.log (2 * Real.cosh (β * J)) ∧
      freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
      freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  ⟨freeEnergy_high_temp_h_zero_lower_bound G J β hβJ hne,
   freeEnergy_high_temp_h_zero_upper_bound G J β hβJ hne,
   by
     have := freeEnergy_J_zero G (0 : ℝ) β hne
     simpa [mul_zero, Real.cosh_zero] using this,
   freeEnergy_beta_zero G J 0 hne⟩

/-- **Single-edge subset is in the FV (3.46) numerator filter at `A = {i, j}`**:
for `i ≠ j` and an edge `e = s(i, j) ∈ G.edgeSet`, the singleton
`{e} ⊆ G.edgeFinset` satisfies the parity predicate: at `v = i, j`,
`1_{v ∈ A} + 1 = 2` is even; at any other `v`, `0 + 0 = 0` is even.
This is the key combinatorial fact behind the single-edge lower bound
`tanh(βJ) ≤ ∑_{X : ∂X = {i,j}} tanh^|X|`. -/
theorem singleton_edge_mem_high_temp_pair_filter
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i j : ι) (hij : i ≠ j) (he : s(i, j) ∈ G.edgeSet) :
    ({s(i, j)} : Finset (Sym2 ι)) ∈ G.edgeFinset.powerset.filter
      (fun X : Finset (Sym2 ι) => ∀ v : ι,
        Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
              + (X.filter (v ∈ ·)).card)) := by
  classical
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · -- {s(i, j)} ⊆ G.edgeFinset
    rw [Finset.mem_powerset, Finset.singleton_subset_iff]
    exact (SimpleGraph.mem_edgeFinset).mpr he
  · -- parity predicate holds for every v
    intro v
    by_cases hv : v ∈ ({i, j} : Finset ι)
    · -- v ∈ {i, j}: 1 + 1 = 2 is even
      rw [if_pos hv]
      have : ({s(i, j)} : Finset (Sym2 ι)).filter (v ∈ ·) = {s(i, j)} := by
        rw [Finset.filter_singleton, if_pos]
        rcases Finset.mem_insert.mp hv with hi | hj
        · subst hi; exact Sym2.mem_mk_left _ _
        · rw [Finset.mem_singleton] at hj; subst hj; exact Sym2.mem_mk_right _ _
      rw [this, Finset.card_singleton]; exact ⟨1, rfl⟩
    · -- v ∉ {i, j}: 0 + 0 = 0 is even
      rw [if_neg hv]
      have : ({s(i, j)} : Finset (Sym2 ι)).filter (v ∈ ·) = ∅ := by
        rw [Finset.filter_singleton, if_neg]
        intro hv_in
        apply hv
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact (Sym2.mem_iff.mp hv_in)
      rw [this, Finset.card_empty]; exact ⟨0, rfl⟩

/-- **Pair correlation single-edge tanh lower bound (GJ §18.3 / FV (3.46))**:
under `0 ≤ β·J` and an edge `s(i, j) ∈ G.edgeSet`,
`⟨σ_iσ_j⟩^{⟨J,0,β⟩} ≥ tanh(β·J) / 2^|E|`.

The single edge `e = s(i, j)` contributes `tanh(β·J)` to the FV (3.46)
numerator; the denominator is bounded above by `2^|E|`
(Step 319). Provides a quantitative non-trivial lower bound: at high
temperature, the pair correlation between adjacent sites does not
vanish faster than `tanh(βJ) / 2^|E|`. -/
theorem correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J)
    (i j : ι) (hij : i ≠ j) (he : s(i, j) ∈ G.edgeSet) :
    Real.tanh (β * J) / (2 : ℝ) ^ G.edgeFinset.card
      ≤ correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) := by
  classical
  rw [correlation_high_temp_expansion_h_zero_closed]
  -- Goal: tanh / 2^|E| ≤ N / D
  set N : ℝ := ∑ X ∈ G.edgeFinset.powerset.filter
      (fun X : Finset (Sym2 ι) => ∀ v : ι,
        Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
              + (X.filter (v ∈ ·)).card)),
      Real.tanh (β * J) ^ X.card with hN_def
  set D : ℝ := ∑ X ∈ G.edgeFinset.powerset.filter
      (fun X : Finset (Sym2 ι) => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
      Real.tanh (β * J) ^ X.card with hD_def
  have h_tanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg
      (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  have h_one_le_D : 1 ≤ D := one_le_sum_pow_tanh_even_subgraph G J β hβJ
  have h_D_pos : 0 < D := lt_of_lt_of_le zero_lt_one h_one_le_D
  have h_D_le : D ≤ (2 : ℝ) ^ G.edgeFinset.card :=
    sum_pow_tanh_even_subgraph_le_two_pow G J β hβJ
  have h_tanh_le_N : Real.tanh (β * J) ≤ N := by
    -- Singleton edge {s(i,j)} contributes tanh^1 to N; other terms ≥ 0.
    have h_mem := singleton_edge_mem_high_temp_pair_filter G i j hij he
    have h_term_eq : Real.tanh (β * J) ^ ({s(i, j)} : Finset (Sym2 ι)).card =
        Real.tanh (β * J) := by rw [Finset.card_singleton, pow_one]
    have h_terms_nn : ∀ X ∈ G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) => ∀ v : ι,
          Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)),
        0 ≤ Real.tanh (β * J) ^ X.card := fun X _ => pow_nonneg h_tanh_nn _
    calc Real.tanh (β * J)
        = Real.tanh (β * J) ^ ({s(i, j)} : Finset (Sym2 ι)).card := h_term_eq.symm
      _ ≤ N := Finset.single_le_sum (f := fun X : Finset (Sym2 ι) =>
                Real.tanh (β * J) ^ X.card) h_terms_nn h_mem
  -- tanh / 2^|E| ≤ tanh / D ≤ N / D
  have h_step1 : Real.tanh (β * J) / (2 : ℝ) ^ G.edgeFinset.card
      ≤ Real.tanh (β * J) / D :=
    div_le_div_of_nonneg_left h_tanh_nn h_D_pos h_D_le
  have h_step2 : Real.tanh (β * J) / D ≤ N / D :=
    div_le_div_of_nonneg_right h_tanh_le_N h_D_pos.le
  exact h_step1.trans h_step2

/-- **Pair correlation strict positivity under edge (GJ §18.3 / FV (3.46))**:
under `0 < β·J` and an edge `s(i, j) ∈ G.edgeSet`,
`0 < ⟨σ_iσ_j⟩^{⟨J,0,β⟩}`.

Direct from `correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges`
(Step 386) and `Real.tanh_pos` at `0 < β·J`. Strengthens GKS-I in this
specific setting: the pair correlation between adjacent sites is
*strictly* positive at any non-trivial high-temperature parameters. -/
theorem correlation_high_temp_h_zero_at_pair_pos_of_edge
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J)
    (i j : ι) (hij : i ≠ j) (he : s(i, j) ∈ G.edgeSet) :
    0 < correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) := by
  have h_tanh_pos : 0 < Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hβJ) (Real.cosh_pos _)
  have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ G.edgeFinset.card := pow_pos (by norm_num) _
  have h_lb_pos : 0 < Real.tanh (β * J) / (2 : ℝ) ^ G.edgeFinset.card :=
    div_pos h_tanh_pos h_pow_pos
  exact lt_of_lt_of_le h_lb_pos
    (correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
      G J β hβJ.le i j hij he)

/-- **Ferromagnetic pair correlation single-edge tanh lower bound (GJ §18.3 / FV (3.46))**:
under `0 ≤ J, 0 < β` and an edge `s(i, j) ∈ G.edgeSet`,
`⟨σ_iσ_j⟩^{⟨J,0,β⟩} ≥ tanh(β·J) / 2^|E|`. Bridges the
`Ferromagnetic`-style hypotheses with
`correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges` via
`mul_nonneg hβ.le hJ`. -/
theorem correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (i j : ι) (hij : i ≠ j) (he : s(i, j) ∈ G.edgeSet) :
    Real.tanh (β * J) / (2 : ℝ) ^ G.edgeFinset.card
      ≤ correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) :=
  correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    G J β (mul_nonneg hβ.le hJ) i j hij he

/-- **Ferromagnetic pair correlation strict positivity under edge (GJ §18.3 / FV (3.46))**:
under `0 < J, 0 < β` and an edge `s(i, j) ∈ G.edgeSet`,
`0 < ⟨σ_iσ_j⟩^{⟨J,0,β⟩}`. Bridges strict-ferromagnetic hypotheses with
`correlation_high_temp_h_zero_at_pair_pos_of_edge` via `mul_pos hβ hJ`. -/
theorem correlation_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β)
    (i j : ι) (hij : i ≠ j) (he : s(i, j) ∈ G.edgeSet) :
    0 < correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) :=
  correlation_high_temp_h_zero_at_pair_pos_of_edge
    G J β (mul_pos hβ hJ) i j hij he

/-- **Pair correlation under `Ferromagnetic` at h = 0**: under ferromagnetic
parameters `⟨J, 0, β⟩` (i.e. `0 ≤ J, 0 < β`),
`0 ≤ ⟨σ_i σ_j⟩ ≤ 1`. Bridges the `Ferromagnetic` typeclass and FV (3.46)
nonneg/upper-bound. -/
theorem correlation_high_temp_h_zero_at_pair_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ι) :
    0 ≤ correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ∧
      correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ≤ 1 :=
  correlation_high_temp_h_zero_at_pair_sandwich G J β
    (mul_nonneg hβ.le hJ) i j

/-- **Pair correlation high-temp closed form (FV (3.46) at A = {i,j})**:
for `i ≠ j` and at `h = 0`,
`⟨σ_i σ_j⟩_{β,0} = (∑_{X : ∂X = {i,j}} tanh^|X|) / (∑_{X : ∂X = ∅} tanh^|X|)`.

Direct instantiation of `correlation_high_temp_expansion_h_zero_closed`
(Step 284) at `A = {i, j}`. Useful concrete case of the
two-point function formula. -/
theorem correlation_high_temp_h_zero_at_pair
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) =
      (∑ X ∈ G.edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ι) => ∀ v : ι,
            Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) /
      (∑ X ∈ G.edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ι) => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) :=
  correlation_high_temp_expansion_h_zero_closed G J β {i, j}

/-- **Magnetization at h = 0 vanishes via FV (3.46) handshake**:
specialization of `correlation_high_temp_h_zero_odd_card_eq_zero` (Step 298)
at `A = {i}`. Since `|{i}| = 1` is odd, the FV (3.46) numerator filter
is empty by handshake, so `⟨σ_i⟩ = 0`. -/
theorem correlation_high_temp_h_zero_at_singleton
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) (i : ι) :
    correlation G ⟨J, 0, β⟩ ({i} : Finset ι) = 0 := by
  refine correlation_high_temp_h_zero_odd_card_eq_zero G J β {i} ?_
  rw [Finset.card_singleton]
  exact ⟨0, rfl⟩

/-- **Singleton vanish + ≤ 1 sandwich at h = 0**: trivial since the
correlation is exactly 0 at h = 0 (Z₂ symmetry). -/
theorem correlation_high_temp_h_zero_at_singleton_eq_zero_le_one
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i : ι) :
    correlation G ⟨J, 0, β⟩ ({i} : Finset ι) = 0 ∧
      correlation G ⟨J, 0, β⟩ ({i} : Finset ι) ≤ 1 :=
  ⟨correlation_high_temp_h_zero_at_singleton G J β i,
   (correlation_high_temp_h_zero_at_singleton G J β i).symm ▸ zero_le_one⟩

/-- **Singleton magnetization under ferromagnetic at h = 0**:
under `0 ≤ J, 0 < β`, `⟨σ_i⟩_{β,0} = 0`. Trivial wrap of Step 331. -/
theorem correlation_high_temp_h_zero_at_singleton_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (_hJ : 0 ≤ J) (_hβ : 0 < β) (i : ι) :
    correlation G ⟨J, 0, β⟩ ({i} : Finset ι) = 0 :=
  correlation_high_temp_h_zero_at_singleton G J β i

/-- **Pair + singleton bundle at h = 0**: combines pair sandwich with
singleton vanishing in a single statement. -/
theorem correlation_high_temp_h_zero_at_pair_singleton_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i} : Finset ι) = 0 ∧
      0 ≤ correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ∧
      correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ≤ 1 :=
  ⟨correlation_high_temp_h_zero_at_singleton G J β i,
   correlation_high_temp_h_zero_at_pair_nonneg G J β hβJ i j,
   correlation_high_temp_h_zero_at_pair_le_one G J β i j⟩

/-- **Pair trivial-slices bundle at h = 0**: at `J = 0` and at `β = 0`,
the pair correlation vanishes. Bundles
`correlation_high_temp_h_zero_at_pair_J_zero` and
`correlation_high_temp_h_zero_at_pair_beta_zero` into one statement. -/
theorem correlation_high_temp_h_zero_at_pair_trivial_slices_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j : ι) :
    correlation G ⟨0, 0, β⟩ ({i, j} : Finset ι) = 0 ∧
      correlation G ⟨J, 0, 0⟩ ({i, j} : Finset ι) = 0 :=
  ⟨correlation_high_temp_h_zero_at_pair_J_zero G β i j,
   correlation_high_temp_h_zero_at_pair_beta_zero G J i j⟩

/-- **Singleton trivial-slices bundle at h = 0**: at `J = 0` and at
`β = 0`, the singleton magnetization vanishes. Bundles
`correlation_high_temp_h_zero_at_singleton_J_zero` and
`correlation_high_temp_h_zero_at_singleton_beta_zero`. -/
theorem correlation_high_temp_h_zero_at_singleton_trivial_slices_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i : ι) :
    correlation G ⟨0, 0, β⟩ ({i} : Finset ι) = 0 ∧
      correlation G ⟨J, 0, 0⟩ ({i} : Finset ι) = 0 :=
  ⟨correlation_high_temp_h_zero_at_singleton_J_zero G β i,
   correlation_high_temp_h_zero_at_singleton_beta_zero G J i⟩

/-- **Pair + singleton trivial-slices full bundle at h = 0**: at
`J = 0` and at `β = 0`, both pair and singleton correlations vanish.
Combines the pair and singleton trivial-slices bundles. -/
theorem correlation_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j : ι) :
    correlation G ⟨0, 0, β⟩ ({i} : Finset ι) = 0 ∧
      correlation G ⟨J, 0, 0⟩ ({i} : Finset ι) = 0 ∧
      correlation G ⟨0, 0, β⟩ ({i, j} : Finset ι) = 0 ∧
      correlation G ⟨J, 0, 0⟩ ({i, j} : Finset ι) = 0 :=
  ⟨correlation_high_temp_h_zero_at_singleton_J_zero G β i,
   correlation_high_temp_h_zero_at_singleton_beta_zero G J i,
   correlation_high_temp_h_zero_at_pair_J_zero G β i j,
   correlation_high_temp_h_zero_at_pair_beta_zero G J i j⟩

/-- **Pair + singleton bundle under ferromagnetic at h = 0**: under
ferromagnetic parameters `⟨J, 0, β⟩` (i.e. `0 ≤ J, 0 < β`), packages
`⟨σ_i⟩ = 0`, `0 ≤ ⟨σ_iσ_j⟩`, and `⟨σ_iσ_j⟩ ≤ 1` into a single triple.
Bridges the `Ferromagnetic` typeclass and the bundle of Step 339 via
`mul_nonneg hβ.le hJ`. -/
theorem correlation_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i} : Finset ι) = 0 ∧
      0 ≤ correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ∧
      correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ≤ 1 :=
  correlation_high_temp_h_zero_at_pair_singleton_bundle G J β
    (mul_nonneg hβ.le hJ) i j

/-- **Pair + singleton complete-summary bundle at h = 0**: a single
statement bundling all known §18.3 properties at `A ∈ {{i}, {i, j}}`:
  1. `⟨σ_iσ_j⟩ ≤ 1` (unconditional upper bound),
  2. `0 ≤ ⟨σ_iσ_j⟩` (sandwich lower under `0 ≤ β·J`),
  3. `⟨σ_i⟩ = 0` (singleton vanishing, unconditional via Z₂ symmetry),
  4. `⟨σ_iσ_j⟩^{⟨0,0,β⟩} = 0` (pair vanishing at trivial slice `J = 0`),
  5. `⟨σ_iσ_j⟩^{⟨J,0,0⟩} = 0` (pair vanishing at trivial slice `β = 0`).
Useful for downstream applications that want a single import for the
qualitative behaviour of pair / singleton correlations at `h = 0`. -/
theorem correlation_high_temp_h_zero_at_pair_singleton_complete_summary
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ≤ 1 ∧
      0 ≤ correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ∧
      correlation G ⟨J, 0, β⟩ ({i} : Finset ι) = 0 ∧
      correlation G ⟨0, 0, β⟩ ({i, j} : Finset ι) = 0 ∧
      correlation G ⟨J, 0, 0⟩ ({i, j} : Finset ι) = 0 :=
  ⟨correlation_high_temp_h_zero_at_pair_le_one G J β i j,
   correlation_high_temp_h_zero_at_pair_nonneg G J β hβJ i j,
   correlation_high_temp_h_zero_at_singleton G J β i,
   correlation_high_temp_h_zero_at_pair_J_zero G β i j,
   correlation_high_temp_h_zero_at_pair_beta_zero G J i j⟩

/-- **High-temperature parameter**: `t = tanh(βJ)`.
For `βJ ≥ 0`, `t ∈ [0, 1)`, and the high-temperature expansion
converges when `t` is small. -/
noncomputable def highTempParam (β J : ℝ) : ℝ := Real.tanh (β * J)

/-- The high-temperature parameter satisfies `|t| < 1` for all finite `βJ`. -/
theorem abs_highTempParam_lt_one (β J : ℝ) :
    |highTempParam β J| < 1 := by
  unfold highTempParam
  exact abs_tanh_lt_one (β * J)

/-- The high-temperature parameter is strictly less than 1. -/
theorem highTempParam_lt_one (β J : ℝ) :
    highTempParam β J < 1 := by
  unfold highTempParam
  exact tanh_lt_one (β * J)

/-- **`highTempParam` is nonneg under `0 ≤ β·J`**: `0 ≤ tanh(β·J)`. -/
theorem highTempParam_nonneg {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 ≤ highTempParam β J := by
  unfold highTempParam
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le

/-- **`highTempParam` is strictly positive under `0 < β·J`**: `0 < tanh(β·J)`. -/
theorem highTempParam_pos {β J : ℝ} (hβJ : 0 < β * J) :
    0 < highTempParam β J := by
  unfold highTempParam
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hβJ) (Real.cosh_pos _)

/-- **`highTempParam` vanishes at `β = 0`**: `highTempParam 0 J = 0`. -/
@[simp] theorem highTempParam_at_beta_zero (J : ℝ) :
    highTempParam 0 J = 0 := by
  unfold highTempParam; rw [zero_mul]; exact Real.tanh_zero

/-- **`highTempParam` vanishes at `J = 0`**: `highTempParam β 0 = 0`. -/
@[simp] theorem highTempParam_at_J_zero (β : ℝ) :
    highTempParam β 0 = 0 := by
  unfold highTempParam; rw [mul_zero]; exact Real.tanh_zero

/-- **Pair correlation single-edge `highTempParam` lower bound**:
restatement of Step 386 in terms of `highTempParam`. Under `0 ≤ β·J`
and an edge `s(i, j) ∈ G.edgeSet`,
`⟨σ_iσ_j⟩^{⟨J,0,β⟩} ≥ highTempParam β J / 2^|E|`. -/
theorem correlation_high_temp_h_zero_at_pair_ge_highTempParam_div_two_pow_edges
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J)
    (i j : ι) (hij : i ≠ j) (he : s(i, j) ∈ G.edgeSet) :
    highTempParam β J / (2 : ℝ) ^ G.edgeFinset.card
      ≤ correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) := by
  unfold highTempParam
  exact correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    G J β hβJ i j hij he


end IsingModel
