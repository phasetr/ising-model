import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.Contraction

/-!
# Theorem eta-le-1 split — Phases 8-10 main theorem and cluster property

Part of the split eta<=1 polynomial-to-exponential decay layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Phase 8: Auxiliary lemmas -/

/-- **Rewrite `p` using `hh`**: for any `p : IsingParams ℝ` with `hh : p.h = 0`,
`p = ⟨p.J, 0, p.β⟩`. Used to apply theorems stated for `⟨J, 0, β⟩`. -/
private theorem isingParams_h_zero (p : IsingParams ℝ) (hh : p.h = 0) :
    p = (⟨p.J, 0, p.β⟩ : IsingParams ℝ) := by cases p; simp_all

/-- **BddAbove for the shell supremum**: the set of values
`{corr∞{0, y.val} : y : {y // n ≤ dist(0,y) ∧ y ≠ 0}}` is bounded above by `1`.

Used in `le_ciSup_of_le` calls to show the `iSup` is well-defined. -/
private theorem shellSup_bddAbove (d n : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) :
    BddAbove (Set.range (fun (y :
        {y : Fin d → ℤ // n ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}) =>
      correlationInfinite (IsingModel.latticeGraph d) Λ p
        {(0 : Fin d → ℤ), y.val})) :=
  ⟨1, fun _x ↦ by
    rintro ⟨y, rfl⟩
    exact correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p _⟩

/-- **Exponential contraction bound for `α^k`**: if `0 < α < 1`, `s > 0`, and `k = n / s`
(natural number floor division), then `α ^ k ≤ (1 / α) * Real.exp (Real.log α / s * n)`.

**Proof**: Set `k = n / s`. The key inequality is that `n / s` (real division) is strictly
less than `k + 1`, which follows from `n < (k + 1) * s` (a standard property of floor
division: `s * (n / s) + n % s = n` and `n % s < s`).  Since `log α < 0` and `n/s < k+1`,
multiplying by `log α` reverses the inequality:
`(k+1) * log α ≤ (n/s) * log α`.
Therefore `α^(k+1) = exp((k+1) * log α) ≤ exp(n/s * log α) = exp(log α / s * n)`.
Finally `α^k = (1/α) * α^(k+1) ≤ (1/α) * exp(log α / s * n)`. -/
private theorem pow_div_le_inv_mul_exp (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (s : ℕ) (hs_pos : 0 < s) (n : ℕ) :
    α ^ (n / s) ≤ (1 / α) * Real.exp (Real.log α / s * n) := by
  have hlog_neg : Real.log α < 0 := Real.log_neg hα_pos hα_lt_one
  -- n < (n / s + 1) * s  follows from n = s*(n/s) + n%s and n%s < s
  have hlt_nat : n < (n / s + 1) * s := by
    have h1 : s * (n / s) + n % s = n := Nat.div_add_mod n s
    have h2 : n % s < s := Nat.mod_lt n hs_pos
    nlinarith
  -- (n : ℝ) / (s : ℝ) < (n / s : ℕ) + 1
  have hlt_real : (n : ℝ) / (s : ℝ) < ((n / s : ℕ) : ℝ) + 1 := by
    have : ((n : ℕ) : ℝ) < ((((n / s + 1) * s : ℕ) : ℕ) : ℝ) := by exact_mod_cast hlt_nat
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hs_pos)]
    push_cast at this ⊢; linarith
  -- (k+1) * log α ≤ (n/s) * log α  (log α < 0 reverses the inequality)
  have hineq : (((n / s : ℕ) : ℝ) + 1) * Real.log α ≤ (n : ℝ) / (s : ℝ) * Real.log α :=
    mul_le_mul_of_nonpos_right (le_of_lt hlt_real) (le_of_lt hlog_neg)
  -- log α / s * n = (n / s) * log α  (rearrangement)
  have hrearr : Real.log α / (s : ℝ) * (n : ℝ) = (n : ℝ) / (s : ℝ) * Real.log α := by ring
  -- α^(n/s+1) ≤ exp(log α / s * n)
  have hpow_le : α ^ (n / s + 1) ≤ Real.exp (Real.log α / (s : ℝ) * (n : ℝ)) := by
    have hpow_eq : α ^ (n / s + 1) = Real.exp (Real.log α * (((n / s : ℕ) : ℝ) + 1)) := by
      rw [← Real.rpow_natCast α (n / s + 1), Real.rpow_def_of_pos hα_pos]
      push_cast; ring
    rw [hpow_eq, hrearr]
    exact Real.exp_le_exp.mpr (by linarith [mul_comm (Real.log α) (((n / s : ℕ) : ℝ) + 1)])
  -- α^(n/s) = (1/α) * α^(n/s+1) ≤ (1/α) * exp(log α / s * n)
  calc α ^ (n / s)
      = (1 / α) * α ^ (n / s + 1) := by field_simp; ring
    _ ≤ (1 / α) * Real.exp (Real.log α / (s : ℝ) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow_le (by positivity)

/-! ## Phase 9: Main theorem -/

/-- **GJ §17.8 Theorem 17.8.1** (η ≤ 1, polynomial decay implies exponential decay):

For a `d`-dimensional ferromagnetic Ising model at `h = 0`, if the
infinite-volume two-point function decays polynomially in the sense of
`HasPolynomialDecay d Λ p`, then it decays exponentially, i.e., the
lattice mass is positive:

  `∃ m > 0, HasExponentialDecay d Λ p m`

## Proof structure

1. **Find a contraction radius `R`**: By `polynomialDecay_contraction_factor_tendsto`,
   `contractionFactor d Λ p r → 0 < 1`, so there exists `R : ℕ` with
   `contractionFactor d Λ p R < 1/2`.

2. **Set `α = contractionFactor d Λ p R`**: We have `0 ≤ α < 1`.

3. **Handle `α = 0`**: Use `m = 1`, `C = exp(R+2)`.
   For `dist(i,j) < R+2`: bound `|corr| ≤ 1 ≤ exp(R+2) * exp(-dist)`.
   For `dist(i,j) ≥ R+2`: `corr∞ = 0` by `shellSup_iterated_bound` with `k=1`, `α^1 = 0`.

4. **Handle `0 < α < 1`**: Set `s = R + 2`, `m = -log(α)/s > 0`, `C = 1/α`.

5. **Pointwise bound via shells**: For any `x` with `dist(0, x) = n ≥ 1`,
   set `k = n / s`. By `shellSup_iterated_bound`, `corr∞{0, x} ≤ α^k`.

6. **Convert to exponential**: By `pow_div_le_inv_mul_exp`,
   `α^k ≤ (1/α) * exp(-m * n) = C * exp(-m * dist(i,j))`.

7. **Apply `truncated2Infinite_eq_correlationInfinite_pair_h_zero`**: At `h = 0`,
   `|truncated2Infinite G Λ p i j| = corr∞{i, j}` (non-negative).

8. **Translation invariance**: `corr∞{i, j} = corr∞{0, j-i}` by
   `correlationInfinite_vaddFinset_of_translationInvariant` with `t = i`.

## Reference

Glimm–Jaffe, *Quantum Physics* 2nd ed., §17.8 pp. 316–318, Springer 1987. -/
theorem correlationInfinite_polynomial_implies_exponential
    (d : ℕ) (hd : 1 ≤ d)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hpoly : HasPolynomialDecay d Λ p) :
    ∃ m : ℝ, 0 < m ∧ HasExponentialDecay d Λ p m := by
  -- Step 1: Extract contraction radius R with α_R < 1/2.
  have hcf_tendsto := polynomialDecay_contraction_factor_tendsto d hd Λ p hf hh hpoly
  rw [Metric.tendsto_atTop] at hcf_tendsto
  obtain ⟨R₀, hR⟩ := hcf_tendsto (1 / 2) (by norm_num)
  -- Take `R := max R₀ 1` so that `1 ≤ R` (needed for `shellSup_iterated_bound`,
  -- whose underlying `ball_boundary_tight_infinite` is false at `r = 0`).
  set R := max R₀ 1 with hRdef
  have hRge1 : 1 ≤ R := le_max_right _ _
  have hR_val : |contractionFactor d Λ p R - 0| < 1 / 2 := hR R (le_max_left _ _)
  simp only [sub_zero] at hR_val
  have hα_lt_half : contractionFactor d Λ p R < 1 / 2 := lt_of_abs_lt hR_val
  have hα_lt_one : contractionFactor d Λ p R < 1 := lt_trans hα_lt_half (by norm_num)
  have hα_nonneg : 0 ≤ contractionFactor d Λ p R := contractionFactor_nonneg d Λ p hf R
  set α := contractionFactor d Λ p R with hα_def
  -- Step 2: Case split on α = 0 or 0 < α < 1.
  rcases eq_or_lt_of_le hα_nonneg with hα_zero | hα_pos
  · -- Case α = 0: Use m = 1, C = exp(R+2).
    -- For dist(i,j) < R+2: |corr| ≤ 1 ≤ exp(R+2) * exp(-dist).
    -- For dist(i,j) ≥ R+2: corr∞{0,j-i} = 0 by shellSup_iterated_bound with k=1, α^1=0.
    refine ⟨1, one_pos, Real.exp (R + 2 : ℕ), (Real.exp_pos _).le, fun i j hij => ?_⟩
    -- At h = 0, |truncated2Infinite| = correlationInfinite.
    have htrunc : truncated2Infinite (IsingModel.latticeGraph d) Λ p i j
        = correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j} := by
      have hp_eq : p = (⟨p.J, 0, p.β⟩ : IsingParams ℝ) := by
        obtain ⟨J, h, β⟩ := p; simp only at hh ⊢; subst hh; rfl
      conv_lhs => rw [hp_eq]
      conv_rhs => rw [hp_eq]
      exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ p.J p.β i j
    rw [htrunc]
    have hcorr_nn : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j} :=
      correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _
    rw [abs_of_nonneg hcorr_nn]
    -- Translation invariance: corr∞{i, j} = corr∞{0, j-i}.
    have htrans : correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j}
        = correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), j - i} := by
      rw [show ({i, j} : Finset (Fin d → ℤ)) = vaddFinset i {(0 : Fin d → ℤ), j - i} from by
        rw [vaddFinset_pair]; simp [vadd_eq_add]]
      exact correlationInfinite_vaddFinset_of_translationInvariant
        (IsingModel.latticeGraph d) Λ i p hf {(0 : Fin d → ℤ), j - i}
    rw [htrans]
    have hdist_eq : IsingModel.latticeDistance d i j = IsingModel.latticeDistance d 0 (j - i) := by
      unfold IsingModel.latticeDistance
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [Pi.zero_apply, zero_sub, Pi.sub_apply]
      congr 1; ring
    set n := IsingModel.latticeDistance d 0 (j - i) with hn_def
    have hjmi_ne : j - i ≠ 0 := fun h => hij (by
      have : j = i + (j - i) := by abel
      rw [h, add_zero] at this; exact this.symm)
    -- Case split: small or large distance.
    rcases Nat.lt_or_ge n (R + 2) with hdist_small | hdist_large
    · -- Small distance (n < R+2): bound corr∞ ≤ 1 ≤ exp(R+2) * exp(-1 * dist(i,j)).
      calc correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), j - i}
          ≤ 1 := correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p _
        _ ≤ Real.exp (↑(R + 2)) * Real.exp (-1 * (IsingModel.latticeDistance d i j : ℝ)) := by
            rw [← Real.exp_add, Real.one_le_exp_iff, hdist_eq]
            have h2r : (n : ℝ) < ((R : ℝ) + 2) := by exact_mod_cast hdist_small
            have h3 : ((R + 2 : ℕ) : ℝ) = (R : ℝ) + 2 := by push_cast; ring
            push_cast [hn_def, h3]; linarith
    · -- Large distance (n ≥ R+2): corr∞{0, j-i} = 0 by the iterated bound with α^1 = 0.
      have hcorr_zero : correlationInfinite (IsingModel.latticeGraph d) Λ p
          {(0 : Fin d → ℤ), j - i} = 0 := by
        -- shellSup_iterated_bound with k=1, n ≥ R+2 gives iSup ≤ α^1 = 0.
        have h_iter := shellSup_iterated_bound d hd R hRge1 Λ p hf hh hα_lt_one 1 n
          (by omega : 1 * (R + 2) ≤ n)
        -- After `set α := contractionFactor d Λ p R`, h_iter uses α.
        have hαpow : α ^ 1 = 0 := by simp [← hα_zero]
        rw [hαpow] at h_iter
        -- corr∞{0, j-i} ≤ iSup ≤ 0, combined with nonnegativity.
        have hle_iSup : correlationInfinite (IsingModel.latticeGraph d) Λ p
            {(0 : Fin d → ℤ), j - i} ≤
            ⨆ (y : {y : Fin d → ℤ // n ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}),
              correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y.val} :=
          le_ciSup_of_le (shellSup_bddAbove d n Λ p) ⟨j - i, le_refl n, hjmi_ne⟩ (le_refl _)
        have hnn : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p
            {(0 : Fin d → ℤ), j - i} :=
          correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _
        linarith [hle_iSup.trans h_iter]
      rw [hcorr_zero]
      exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  · -- Case 0 < α < 1.
    -- Step 3: Set step size s = R + 2, mass m = -log(α)/s > 0, constant C = 1/α.
    set s := R + 2 with hs_def
    have hs_pos : (0 : ℕ) < s := by omega
    have hs_pos_r : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr hs_pos
    have hlog_neg : Real.log α < 0 := Real.log_neg hα_pos hα_lt_one
    set m := -Real.log α / (s : ℝ) with hm_def
    have hm_pos : 0 < m := div_pos (neg_pos.mpr hlog_neg) hs_pos_r
    set C := 1 / α with hC_def
    have hC_pos : 0 < C := div_pos one_pos hα_pos
    -- Step 4: Witness m and C for HasExponentialDecay.
    refine ⟨m, hm_pos, C, hC_pos.le, fun i j hij => ?_⟩
    -- Step 5: At h = 0, |truncated2Infinite| = correlationInfinite.
    have htrunc : truncated2Infinite (IsingModel.latticeGraph d) Λ p i j
        = correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j} := by
      have hp_eq : p = (⟨p.J, 0, p.β⟩ : IsingParams ℝ) := by cases p; simp_all
      conv_lhs => rw [hp_eq]
      conv_rhs => rw [hp_eq]
      exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ p.J p.β i j
    rw [htrunc]
    have hcorr_nn : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j} :=
      correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _
    rw [abs_of_nonneg hcorr_nn]
    -- Step 6: Translation invariance — corr∞{i, j} = corr∞{0, j - i}.
    -- Use t = i: by vaddFinset_pair, vaddFinset i {0, j-i} = {i +ᵥ 0, i +ᵥ (j-i)} = {i, j}.
    have htrans : correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j}
        = correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), j - i} := by
      rw [show ({i, j} : Finset (Fin d → ℤ)) = vaddFinset i {(0 : Fin d → ℤ), j - i} from by
        rw [vaddFinset_pair]
        simp [vadd_eq_add]]
      exact correlationInfinite_vaddFinset_of_translationInvariant
        (IsingModel.latticeGraph d) Λ i p hf {(0 : Fin d → ℤ), j - i}
    rw [htrans]
    -- Step 7: Set n = latticeDistance d 0 (j - i) = latticeDistance d i j.
    have hdist : IsingModel.latticeDistance d i j = IsingModel.latticeDistance d 0 (j - i) := by
      unfold IsingModel.latticeDistance
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [Pi.zero_apply, zero_sub, Pi.sub_apply]
      congr 1; ring
    set n := IsingModel.latticeDistance d 0 (j - i) with hn_def
    -- n ≥ 1 since i ≠ j implies j - i ≠ 0.
    have hjmi_ne : j - i ≠ 0 := fun h => hij (by
      have : j = i + (j - i) := by abel
      rw [h, add_zero] at this; exact this.symm)
    have hn_pos : 0 < n := by
      rw [hn_def, Nat.pos_iff_ne_zero]
      simp only [ne_eq, IsingModel.latticeDistance_eq_zero_iff]
      exact fun h => hjmi_ne h.symm
    -- Step 8: Set k = n / s, then k * s ≤ n.
    set k := n / s with hk_def
    have hk_le : k * s ≤ n := Nat.div_mul_le_self n s
    -- Step 9: Apply shellSup_iterated_bound to get corr∞{0, j-i} ≤ α^k.
    have hshell_le : correlationInfinite (IsingModel.latticeGraph d) Λ p
        {(0 : Fin d → ℤ), j - i} ≤ α ^ k := by
      rw [hα_def]
      have h_iter := shellSup_iterated_bound d hd R hRge1 Λ p hf hh hα_lt_one k n hk_le
      apply le_trans _ h_iter
      -- corr∞{0, j-i} is a term in the iSup at shell level n.
      apply le_ciSup_of_le (shellSup_bddAbove d n Λ p)
        ⟨j - i, le_refl n, hjmi_ne⟩
      -- The value at ⟨j-i, ...⟩ is corr∞{0, j-i}: proved by le_refl.
      exact le_refl _
    -- Step 10: Apply pow_div_le_inv_mul_exp to bound α^k ≤ C * exp(-m * n).
    have hαk_le : α ^ k ≤ C * Real.exp (-m * n) := by
      have hpow := pow_div_le_inv_mul_exp α hα_pos hα_lt_one s hs_pos n
      -- pow_div_le_inv_mul_exp gives: α^(n/s) ≤ (1/α) * exp(log α / s * n)
      -- We have k = n/s and C = 1/α and -m * n = log α / s * n.
      rw [← hk_def] at hpow
      rw [hC_def, hm_def]
      have heq : -(-Real.log α / (s : ℝ)) * n = Real.log α / s * n := by
        ring
      rw [heq]
      exact hpow
    -- Step 11: Combine: corr∞{0, j-i} ≤ α^k ≤ C * exp(-m * n) = C * exp(-m * dist(i,j)).
    calc correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), j - i}
        ≤ α ^ k := hshell_le
      _ ≤ C * Real.exp (-m * n) := hαk_le
      _ = C * Real.exp (-m * (IsingModel.latticeDistance d i j : ℝ)) := by rw [← hdist]

/-! ## Phase 10: Cluster property from polynomial decay -/

/-- **Cluster property from polynomial decay** (GJ §5.1 / §17.8 corollary):
For a `d`-dimensional ferromagnetic Ising model at `h = 0`, if the
infinite-volume two-point function has polynomial decay (`HasPolynomialDecay`),
then the cluster property holds: the truncated two-point function
`j ↦ U₂∞(i, j)` tends to `0` along the cofinite filter.

**Proof**: `HasPolynomialDecay` → `HasExponentialDecay` (by
`correlationInfinite_polynomial_implies_exponential`, GJ §17.8 Thm 17.8.1)
→ cluster property (by `clusterProperty_latticeGraph_of_HasExponentialDecay`).

Reference: Glimm–Jaffe §5.1 pp. 76–79; §17.8 pp. 316–318. -/
theorem clusterProperty_latticeGraph_of_polynomialDecay
    (d : ℕ) (hd : 1 ≤ d)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hpoly : HasPolynomialDecay d Λ p) :
    Ambient.clusterProperty (IsingModel.latticeGraph d) Λ p :=
  let ⟨_, hm, hexp⟩ := correlationInfinite_polynomial_implies_exponential d hd Λ p hf hh hpoly
  clusterProperty_latticeGraph_of_HasExponentialDecay d Λ p hm hexp


end Ambient
end IsingModel
