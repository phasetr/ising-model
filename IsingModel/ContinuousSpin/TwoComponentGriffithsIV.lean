import IsingModel.ContinuousSpin.TwoComponentGriffithsIII
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Single-site rotated doubled moment with an external field (GJ Theorem 4.7.1)

The field-dependent product-form single-site moment positivity for the rotated
doubled density: for `A > 0` and non-negative field couplings `c_α, c_γ ≥ 0`,
`0 ≤ ∫_{(Fin 4 → ℝ)} (∏ⱼ pⱼ^{eⱼ})·exp(c_α·p₀ + c_γ·p₂)·rotSiteDensity A σ p`.
This is the per-site engine (with field) for the duplicate-variable proof of the
second/third Griffiths inequalities (4.7.6)–(4.7.8).

The proof mirrors `singleSpinMoment_field_nonneg`: truncate the field
exponentials, expand each truncation into a finite non-negative combination of
`twoComp_single_site_prod_extra_nonneg` moments, and pass to the limit by
dominated convergence (the linear field absorbed into the quadratic part of the
density via `|t| ≤ (1+t²)/2`).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.7, Theorem 4.7.1, pp. 70–71
-/

namespace IsingModel.ContinuousSpin

open Real MeasureTheory

/-- Shifting the quadratic coefficient of the rotated density:
`rotSiteDensity A (σ - d) p = exp(d·∑ⱼ pⱼ²)·rotSiteDensity A σ p`. -/
theorem rotSiteDensity_shift (A σ d : ℝ) (p : Fin 4 → ℝ) :
    rotSiteDensity A (σ - d) p
      = Real.exp (d * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2)) * rotSiteDensity A σ p := by
  simp only [rotSiteDensity, twoCompEvenPart, ← Real.exp_add]
  congr 1
  ring

/-- **Product-form single-site rotated doubled moment positivity with an external
field** (GJ Theorem 4.7.1 (4.7.6)–(4.7.8), pp. 70–71): for `A > 0` and
`c_α, c_γ ≥ 0`,
`0 ≤ ∫_{(Fin 4 → ℝ)} (∏ⱼ pⱼ^{eⱼ})·exp(c_α·p₀ + c_γ·p₂)·rotSiteDensity A σ p`. -/
theorem twoComp_single_site_field_prod_nonneg {A σ cα cγ : ℝ} (hA : 0 < A)
    (hcα : 0 ≤ cα) (hcγ : 0 ≤ cγ) (e : Fin 4 → ℕ) :
    0 ≤ ∫ p : Fin 4 → ℝ,
      (∏ j, p j ^ e j) * Real.exp (cα * p 0 + cγ * p 2) * rotSiteDensity A σ p := by
  classical
  set F : ℕ → (Fin 4 → ℝ) → ℝ := fun N p =>
    (∏ j, p j ^ e j) * expTrunc N (cα * p 0) * expTrunc N (cγ * p 2) * rotSiteDensity A σ p with hF
  -- Each truncation integral is non-negative.
  have hFnn : ∀ N, 0 ≤ ∫ p, F N p := by
    intro N
    have hFeq : ∀ p : Fin 4 → ℝ, F N p
        = ∑ m ∈ Finset.range N, ∑ l ∈ Finset.range N,
            (cα ^ m / m.factorial * (cγ ^ l / l.factorial)) *
              ((∏ j, p j ^ e j) * p 0 ^ m * p 2 ^ l * rotSiteDensity A σ p) := by
      intro p
      have hrw : F N p
          = ((∏ j, p j ^ e j) * rotSiteDensity A σ p) *
              ((∑ m ∈ Finset.range N, (cα * p 0) ^ m / m.factorial) *
               (∑ l ∈ Finset.range N, (cγ * p 2) ^ l / l.factorial)) := by
        simp only [hF, expTrunc]; ring
      rw [hrw, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_pow, mul_pow]; ring
    have hint : ∀ m l : ℕ, Integrable (fun p : Fin 4 → ℝ =>
        (cα ^ m / m.factorial * (cγ ^ l / l.factorial)) *
          ((∏ j, p j ^ e j) * p 0 ^ m * p 2 ^ l * rotSiteDensity A σ p)) := by
      intro m l
      refine Integrable.const_mul ?_ _
      have heq : ∀ p : Fin 4 → ℝ,
          (∏ j, p j ^ e j) * p 0 ^ m * p 2 ^ l * rotSiteDensity A σ p
            = (∏ j, p j ^ (e j + (if j = 0 then m else 0) + (if j = 2 then l else 0)))
                * rotSiteDensity A σ p := fun p => by rw [prod_pow_raise]
      simp_rw [heq]
      exact integrable_monomial_mul_rotSiteDensity hA _
    calc (∫ p, F N p)
        = ∑ m ∈ Finset.range N, ∑ l ∈ Finset.range N,
            (cα ^ m / m.factorial * (cγ ^ l / l.factorial)) *
              ∫ p : Fin 4 → ℝ,
                (∏ j, p j ^ e j) * p 0 ^ m * p 2 ^ l * rotSiteDensity A σ p := by
          simp_rw [hFeq]
          rw [integral_finset_sum _ (fun m _ => integrable_finset_sum _ (fun l _ => hint m l))]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [integral_finset_sum _ (fun l _ => hint m l)]
          exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
      _ ≥ 0 := by
          refine Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun l _ => ?_
          exact mul_nonneg (by positivity) (twoComp_single_site_prod_extra_nonneg σ hA e m l)
  -- Dominated convergence.
  set d : ℝ := max |cα| |cγ| / 2 with hd
  have hbnd_int : Integrable (fun p : Fin 4 → ℝ =>
      Real.exp ((|cα| + |cγ|) / 2)
        * ‖(∏ j, p j ^ e j) * rotSiteDensity A (σ - d) p‖) :=
    ((integrable_monomial_mul_rotSiteDensity (A := A) (σ := σ - d) hA e).norm).const_mul _
  have hlim : Filter.Tendsto (fun N => ∫ p, F N p) Filter.atTop
      (nhds (∫ p : Fin 4 → ℝ,
        (∏ j, p j ^ e j) * Real.exp (cα * p 0 + cγ * p 2) * rotSiteDensity A σ p)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun p => Real.exp ((|cα| + |cγ|) / 2) * ‖(∏ j, p j ^ e j) * rotSiteDensity A (σ - d) p‖)
      (fun N => ?_) hbnd_int (fun N => ?_) ?_
    · -- measurability
      have hc : Continuous (F N) := by
        simp only [hF]
        exact ((((continuous_finset_prod _ fun j _ => (continuous_apply j).pow (e j)).mul
          ((continuous_expTrunc N).comp ((continuous_apply 0).const_mul cα))).mul
          ((continuous_expTrunc N).comp ((continuous_apply 2).const_mul cγ))).mul
            (continuous_rotSiteDensity A σ))
      exact hc.aestronglyMeasurable
    · -- pointwise bound
      refine Filter.Eventually.of_forall fun p => ?_
      have hdens : (0 : ℝ) < rotSiteDensity A σ p := rotSiteDensity_pos A σ p
      have hnormF : ‖F N p‖
          = (∏ j, |p j| ^ e j) * |expTrunc N (cα * p 0)| * |expTrunc N (cγ * p 2)|
            * rotSiteDensity A σ p := by
        simp only [hF, Real.norm_eq_abs, abs_mul, abs_of_pos hdens, Finset.abs_prod, abs_pow]
      rw [hnormF]
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (rotSiteDensity_pos A (σ - d) p),
        Finset.abs_prod, abs_pow]
      have hexple : |expTrunc N (cα * p 0)| * |expTrunc N (cγ * p 2)|
          ≤ Real.exp ((|cα| + |cγ|) / 2)
            * Real.exp (d * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2)) := by
        have h1 : |expTrunc N (cα * p 0)| ≤ Real.exp |cα * p 0| := abs_expTrunc_le_exp_abs _ _
        have h2 : |expTrunc N (cγ * p 2)| ≤ Real.exp |cγ * p 2| := abs_expTrunc_le_exp_abs _ _
        have hle : |cα * p 0| + |cγ * p 2|
            ≤ (|cα| + |cγ|) / 2 + d * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) := by
          rw [abs_mul, abs_mul]
          have ht : |p 0| ≤ (1 + p 0 ^ 2) / 2 := by
            nlinarith [sq_nonneg (|p 0| - 1), sq_abs (p 0), abs_nonneg (p 0)]
          have hq : |p 2| ≤ (1 + p 2 ^ 2) / 2 := by
            nlinarith [sq_nonneg (|p 2| - 1), sq_abs (p 2), abs_nonneg (p 2)]
          have hd1 : |cα| ≤ 2 * d := by rw [hd]; have := le_max_left |cα| |cγ|; linarith
          have hd2 : |cγ| ≤ 2 * d := by rw [hd]; have := le_max_right |cα| |cγ|; linarith
          have hdnn : (0 : ℝ) ≤ d := by rw [hd]; positivity
          nlinarith [mul_le_mul_of_nonneg_left ht (abs_nonneg cα),
            mul_le_mul_of_nonneg_left hq (abs_nonneg cγ),
            mul_nonneg (sq_nonneg (p 0)) (by linarith [hd1] : (0 : ℝ) ≤ 2 * d - |cα|),
            mul_nonneg (sq_nonneg (p 2)) (by linarith [hd2] : (0 : ℝ) ≤ 2 * d - |cγ|),
            mul_nonneg hdnn (sq_nonneg (p 1)), mul_nonneg hdnn (sq_nonneg (p 3))]
        calc |expTrunc N (cα * p 0)| * |expTrunc N (cγ * p 2)|
            ≤ Real.exp |cα * p 0| * Real.exp |cγ * p 2| :=
              mul_le_mul h1 h2 (abs_nonneg _) (Real.exp_pos _).le
          _ = Real.exp (|cα * p 0| + |cγ * p 2|) := (Real.exp_add _ _).symm
          _ ≤ Real.exp ((|cα| + |cγ|) / 2 + d * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2)) :=
              Real.exp_le_exp.mpr hle
          _ = Real.exp ((|cα| + |cγ|) / 2)
                * Real.exp (d * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2)) := Real.exp_add _ _
      rw [rotSiteDensity_shift]
      calc (∏ j, |p j| ^ e j) * |expTrunc N (cα * p 0)| * |expTrunc N (cγ * p 2)|
              * rotSiteDensity A σ p
          = (∏ j, |p j| ^ e j) * rotSiteDensity A σ p
              * (|expTrunc N (cα * p 0)| * |expTrunc N (cγ * p 2)|) := by ring
        _ ≤ (∏ j, |p j| ^ e j) * rotSiteDensity A σ p
              * (Real.exp ((|cα| + |cγ|) / 2)
                * Real.exp (d * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2))) :=
            mul_le_mul_of_nonneg_left hexple
              (mul_nonneg (Finset.prod_nonneg fun j _ => by positivity)
                (rotSiteDensity_pos _ _ _).le)
        _ = Real.exp ((|cα| + |cγ|) / 2)
              * ((∏ j, |p j| ^ e j)
                * (Real.exp (d * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2))
                  * rotSiteDensity A σ p)) := by
            ring
    · -- pointwise convergence
      refine Filter.Eventually.of_forall fun p => ?_
      have htarget : (∏ j, p j ^ e j) * Real.exp (cα * p 0 + cγ * p 2) * rotSiteDensity A σ p
          = ((∏ j, p j ^ e j) * rotSiteDensity A σ p)
            * (Real.exp (cα * p 0) * Real.exp (cγ * p 2)) := by
        rw [Real.exp_add]; ring
      rw [htarget]
      have hFp : (fun N => F N p)
          = fun N => ((∏ j, p j ^ e j) * rotSiteDensity A σ p)
            * (expTrunc N (cα * p 0) * expTrunc N (cγ * p 2)) := by
        funext N; simp only [hF]; ring
      rw [hFp]
      exact tendsto_const_nhds.mul ((tendsto_expTrunc _).mul (tendsto_expTrunc _))
  exact ge_of_tendsto' hlim hFnn

end IsingModel.ContinuousSpin
