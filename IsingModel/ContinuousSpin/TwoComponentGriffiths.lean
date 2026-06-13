import IsingModel.ContinuousSpin.TwoComponentIntegrable
import IsingModel.ContinuousSpin.Phi4Symmetrization
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Two-component single-site moment positivity (GJ §4.7, Griffiths-I core)

The single-site moments of the `SO(2)`-invariant planar-rotator density
`exp(−A·(t²+q²)² − σ·(t²+q²))` are non-negative:
`0 ≤ ∫_{ℝ²} t^a q^b · exp(−A·(t²+q²)² − σ·(t²+q²)) d(t,q)` for `A > 0`. Odd
moments vanish by coordinate reflection; even moments have a non-negative
integrand. This is the single-site building block of the first inequality
(`⟨t^A q^B⟩ ≥ 0`) of GJ Theorem 4.7.1 (Issue #3918).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.7, Theorem 4.7.1, p. 70
-/

namespace IsingModel.ContinuousSpin

open Real MeasureTheory Set
open scoped ENNReal

/-- **Radial integrability with a monomial weight**: `r ↦ r^n · exp(b·r² − A·r⁴)`
is integrable on `(0, ∞)` for any `b ∈ ℝ`, `n ∈ ℕ` when `A > 0`. Completing the
square `b·r² − A·r⁴ ≤ b²/(2A) − (A/2)·r⁴` dominates by `r^n · exp(−(A/2)·r⁴)`,
Mathlib's super-Gaussian with a polynomial factor. -/
theorem integrableOn_pow_quad_quartic {A b : ℝ} (hA : 0 < A) (n : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ n * Real.exp (b * r ^ 2 - A * r ^ 4)) (Ioi 0) := by
  have h2A : (0 : ℝ) < 2 * A := by linarith
  have hsn : (-1 : ℝ) < (n : ℝ) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hbase : IntegrableOn
      (fun r : ℝ => r ^ (n : ℝ) * Real.exp (-(A / 2) * r ^ (4 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow hsn (by norm_num) (by linarith)
  have h4 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  have hbase' : IntegrableOn (fun r : ℝ => r ^ n * Real.exp (-(A / 2) * r ^ 4)) (Ioi 0) := by
    refine hbase.congr_fun (fun r hr => ?_) measurableSet_Ioi
    rw [Real.rpow_natCast, h4, Real.rpow_natCast]
  have hM : IntegrableOn
      (fun r : ℝ => Real.exp (b ^ 2 / (2 * A)) * (r ^ n * Real.exp (-(A / 2) * r ^ 4)))
      (Ioi 0) := hbase'.const_mul _
  refine Integrable.mono' hM ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).restrict
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun r hr => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pow_nonneg (le_of_lt hr) n) (Real.exp_pos _).le)]
    have hid : b * r ^ 2 - A * r ^ 4
        = b ^ 2 / (2 * A) - (A / 2) * r ^ 4 - (A * r ^ 2 - b) ^ 2 / (2 * A) := by
      field_simp; ring
    have key : b * r ^ 2 - A * r ^ 4 ≤ b ^ 2 / (2 * A) + (-(A / 2) * r ^ 4) := by
      rw [hid]
      have : 0 ≤ (A * r ^ 2 - b) ^ 2 / (2 * A) := div_nonneg (sq_nonneg _) (le_of_lt h2A)
      linarith
    calc r ^ n * Real.exp (b * r ^ 2 - A * r ^ 4)
        ≤ r ^ n * Real.exp (b ^ 2 / (2 * A) + (-(A / 2) * r ^ 4)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr key) (pow_nonneg (le_of_lt hr) n)
      _ = Real.exp (b ^ 2 / (2 * A)) * (r ^ n * Real.exp (-(A / 2) * r ^ 4)) := by
          rw [Real.exp_add]; ring

/-- **Integrability of the monomial-weighted single-spin density** over `ℝ²` for
`A > 0`: `ξ ↦ tᵃqᵇ·exp(−A·|ξ|⁴ − σ·|ξ|²)` is integrable. In polar coordinates the
norm is `≤ r^{a+b+1}·exp(−A·r⁴ − σ·r²)` (since `|cosθ|, |sinθ| ≤ 1`), whose radial
integral is finite by `integrableOn_pow_quad_quartic`. -/
theorem integrable_pow_mul_singleSpinDensity {A σ : ℝ} (hA : 0 < A) (a b : ℕ) :
    Integrable (fun ξ : ℝ × ℝ => ξ.1 ^ a * ξ.2 ^ b * singleSpinDensity A σ ξ) := by
  have hmeas : AEStronglyMeasurable
      (fun ξ : ℝ × ℝ => ξ.1 ^ a * ξ.2 ^ b * singleSpinDensity A σ ξ) volume :=
    (((continuous_fst.pow a).mul (continuous_snd.pow b)).mul
      (continuous_singleSpinDensity A σ)).aestronglyMeasurable
  rw [← integrable_norm_iff hmeas,
    ← lintegral_ofReal_ne_top_iff_integrable hmeas.norm
      (Filter.Eventually.of_forall fun _ => norm_nonneg _),
    ← lintegral_comp_polarCoord_symm
      (fun ξ => ENNReal.ofReal ‖ξ.1 ^ a * ξ.2 ^ b * singleSpinDensity A σ ξ‖)]
  -- dominating radial integrand `r^{a+b+1}·exp(−A r⁴ − σ r²)`
  set g : ℝ → ENNReal :=
    fun r => ENNReal.ofReal (r ^ (a + b + 1) * Real.exp (-σ * r ^ 2 - A * r ^ 4)) with hg
  have hbound : ∀ rθ ∈ polarCoord.target,
      ENNReal.ofReal rθ.1 • ENNReal.ofReal
          ‖(polarCoord.symm rθ).1 ^ a * (polarCoord.symm rθ).2 ^ b
            * singleSpinDensity A σ (polarCoord.symm rθ)‖ ≤ g rθ.1 := by
    intro rθ hrθ
    obtain ⟨r, θ⟩ := rθ
    have hr : 0 < r := hrθ.1
    have hpolar : polarCoord.symm (r, θ) = (r * Real.cos θ, r * Real.sin θ) := rfl
    rw [hpolar, smul_eq_mul, ← ENNReal.ofReal_mul (le_of_lt hr), hg]
    refine ENNReal.ofReal_le_ofReal ?_
    have hdens : singleSpinDensity A σ (r * Real.cos θ, r * Real.sin θ)
        = Real.exp (-A * r ^ 4 - σ * r ^ 2) := by
      have := singleSpinDensity_polarCoord_symm A σ (r, θ)
      rwa [hpolar] at this
    have hnorm : ‖(r * Real.cos θ) ^ a * (r * Real.sin θ) ^ b
          * singleSpinDensity A σ (r * Real.cos θ, r * Real.sin θ)‖
        = |r * Real.cos θ| ^ a * |r * Real.sin θ| ^ b * Real.exp (-A * r ^ 4 - σ * r ^ 2) := by
      rw [hdens, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow,
        abs_of_pos (Real.exp_pos _)]
    rw [hnorm]
    have hcle : |r * Real.cos θ| ≤ r := by
      rw [abs_mul, abs_of_pos hr]
      nlinarith [abs_cos_le_one θ, hr.le, abs_nonneg (Real.cos θ)]
    have hsle : |r * Real.sin θ| ≤ r := by
      rw [abs_mul, abs_of_pos hr]
      nlinarith [abs_sin_le_one θ, hr.le, abs_nonneg (Real.sin θ)]
    have hca : |r * Real.cos θ| ^ a ≤ r ^ a := pow_le_pow_left₀ (abs_nonneg _) hcle a
    have hsb : |r * Real.sin θ| ^ b ≤ r ^ b := pow_le_pow_left₀ (abs_nonneg _) hsle b
    have hexp : Real.exp (-A * r ^ 4 - σ * r ^ 2) = Real.exp (-σ * r ^ 2 - A * r ^ 4) := by
      ring_nf
    calc r * (|r * Real.cos θ| ^ a * |r * Real.sin θ| ^ b * Real.exp (-A * r ^ 4 - σ * r ^ 2))
        ≤ r * (r ^ a * r ^ b * Real.exp (-A * r ^ 4 - σ * r ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hr.le
          exact mul_le_mul (mul_le_mul hca hsb (by positivity) (by positivity)) le_rfl
            (Real.exp_pos _).le (by positivity)
      _ = r ^ (a + b + 1) * Real.exp (-σ * r ^ 2 - A * r ^ 4) := by
          rw [hexp, pow_add, pow_add, pow_one]; ring
  have hgcont : Continuous fun r : ℝ => r ^ (a + b + 1) * Real.exp (-σ * r ^ 2 - A * r ^ 4) := by
    fun_prop
  have hgmeas : Measurable g := by rw [hg]; exact hgcont.measurable.ennreal_ofReal
  refine ne_top_of_le_ne_top ?_ (setLIntegral_mono (hgmeas.comp measurable_fst) hbound)
  -- the dominating radial lintegral is finite
  rw [show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π from rfl]
  simp only [Function.comp_apply]
  · have hrad : IntegrableOn
        (fun r : ℝ => r ^ (a + b + 1) * Real.exp (-σ * r ^ 2 - A * r ^ 4)) (Ioi 0) :=
      integrableOn_pow_quad_quartic hA (a + b + 1)
    have hradnn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
        fun r : ℝ => r ^ (a + b + 1) * Real.exp (-σ * r ^ 2 - A * r ^ 4) :=
      (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun r hr =>
        mul_nonneg (pow_nonneg (le_of_lt hr) _) (Real.exp_pos _).le)
    have hrad_fin : (∫⁻ r in Ioi (0 : ℝ), g r) ≠ ∞ :=
      (lintegral_ofReal_ne_top_iff_integrable hrad.aestronglyMeasurable hradnn).mpr hrad
    have hfactor : (∫⁻ rθ in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, g rθ.1)
        = volume (Ioo (-π) π) * ∫⁻ r in Ioi (0 : ℝ), g r := by
      rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
        ← Measure.prod_restrict,
        lintegral_prod (fun rθ : ℝ × ℝ => g rθ.1)
          (hgmeas.comp measurable_fst).aemeasurable]
      simp_rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
      rw [lintegral_mul_const _ hgmeas, mul_comm]
    rw [hfactor]
    exact ENNReal.mul_ne_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) hrad_fin

/-- **Single-site moment positivity** (GJ §4.7 Griffiths-I core): for `A > 0`,
`0 ≤ ∫_{ℝ²} tᵃqᵇ·exp(−A·|ξ|⁴ − σ·|ξ|²)`. Odd `a` (or odd `b`) gives zero by the
`t ↦ −t` (resp. `q ↦ −q`) reflection (the density is even in each coordinate);
even `a, b` give a non-negative integrand. -/
theorem singleSpinMoment_nonneg {A σ : ℝ} (hA : 0 < A) (a b : ℕ) :
    0 ≤ ∫ ξ : ℝ × ℝ, ξ.1 ^ a * ξ.2 ^ b * singleSpinDensity A σ ξ := by
  have hint := integrable_pow_mul_singleSpinDensity (A := A) (σ := σ) hA a b
  rcases Nat.even_or_odd a with ha | ha
  · rcases Nat.even_or_odd b with hb | hb
    · -- both even: non-negative integrand
      refine integral_nonneg (fun ξ => ?_)
      have h1 : 0 ≤ ξ.1 ^ a := ha.pow_nonneg _
      have h2 : 0 ≤ ξ.2 ^ b := hb.pow_nonneg _
      have h3 : 0 < singleSpinDensity A σ ξ := Real.exp_pos _
      positivity
    · -- b odd: reflect the q-coordinate
      rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
        integral_prod _ hint]
      have hodd : ∀ t : ℝ, (∫ q : ℝ, t ^ a * q ^ b * singleSpinDensity A σ (t, q)) = 0 := by
        intro t
        have hflip : ∀ q : ℝ, t ^ a * (-q) ^ b * singleSpinDensity A σ (t, -q)
            = -(t ^ a * q ^ b * singleSpinDensity A σ (t, q)) := by
          intro q
          have hdens : singleSpinDensity A σ (t, -q) = singleSpinDensity A σ (t, q) := by
            simp only [singleSpinDensity]; ring_nf
          rw [hdens, hb.neg_pow]; ring
        have key : (∫ q : ℝ, t ^ a * q ^ b * singleSpinDensity A σ (t, q))
            = -(∫ q : ℝ, t ^ a * q ^ b * singleSpinDensity A σ (t, q)) := by
          calc (∫ q : ℝ, t ^ a * q ^ b * singleSpinDensity A σ (t, q))
              = ∫ q : ℝ, t ^ a * (-q) ^ b * singleSpinDensity A σ (t, -q) :=
                (integral_comp_neg_real
                  (fun q => t ^ a * q ^ b * singleSpinDensity A σ (t, q))).symm
            _ = ∫ q : ℝ, -(t ^ a * q ^ b * singleSpinDensity A σ (t, q)) := by simp_rw [hflip]
            _ = -(∫ q : ℝ, t ^ a * q ^ b * singleSpinDensity A σ (t, q)) := integral_neg _
        linarith [key]
      simp only [hodd, integral_zero, le_refl]
  · -- a odd: reflect the t-coordinate
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
      integral_prod _ hint]
    have hflip : ∀ t : ℝ, (∫ q : ℝ, (-t) ^ a * q ^ b * singleSpinDensity A σ (-t, q))
        = -(∫ q : ℝ, t ^ a * q ^ b * singleSpinDensity A σ (t, q)) := by
      intro t
      rw [← integral_neg]
      congr 1
      ext q
      have hdens : singleSpinDensity A σ (-t, q) = singleSpinDensity A σ (t, q) := by
        simp only [singleSpinDensity]; ring_nf
      rw [hdens, ha.neg_pow]; ring
    have key : (∫ t : ℝ, ∫ q : ℝ, t ^ a * q ^ b * singleSpinDensity A σ (t, q))
        = -(∫ t : ℝ, ∫ q : ℝ, t ^ a * q ^ b * singleSpinDensity A σ (t, q)) := by
      calc (∫ t : ℝ, ∫ q : ℝ, t ^ a * q ^ b * singleSpinDensity A σ (t, q))
          = ∫ t : ℝ, ∫ q : ℝ, (-t) ^ a * q ^ b * singleSpinDensity A σ (-t, q) :=
            (integral_comp_neg_real
              (fun t => ∫ q : ℝ, t ^ a * q ^ b * singleSpinDensity A σ (t, q))).symm
        _ = ∫ t : ℝ, -(∫ q : ℝ, t ^ a * q ^ b * singleSpinDensity A σ (t, q)) := by
            simp_rw [hflip]
        _ = -(∫ t : ℝ, ∫ q : ℝ, t ^ a * q ^ b * singleSpinDensity A σ (t, q)) := integral_neg _
    linarith [key]

/-! ## Single-site moments with an external field (Griffiths-I with `h ≥ 0`) -/

/-- The truncated exponential `∑_{k<N} x^k/k!` (partial sum of the exp series). -/
noncomputable def expTrunc (N : ℕ) (x : ℝ) : ℝ := ∑ k ∈ Finset.range N, x ^ k / k.factorial

/-- The truncated exponential is continuous (a polynomial). -/
theorem continuous_expTrunc (N : ℕ) : Continuous (expTrunc N) := by
  unfold expTrunc; fun_prop

/-- The truncated exponentials converge to `exp`. -/
theorem tendsto_expTrunc (x : ℝ) :
    Filter.Tendsto (fun N => expTrunc N x) Filter.atTop (nhds (Real.exp x)) := by
  have h : HasSum (fun n : ℕ => x ^ n / n.factorial) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  exact h.tendsto_sum_nat

/-- The truncated exponential is bounded in absolute value by `exp |x|`. -/
theorem abs_expTrunc_le_exp_abs (N : ℕ) (x : ℝ) : |expTrunc N x| ≤ Real.exp |x| := by
  have hsum : HasSum (fun n : ℕ => |x| ^ n / n.factorial) (Real.exp |x|) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp |x|
  calc |expTrunc N x| ≤ ∑ k ∈ Finset.range N, |x ^ k / k.factorial| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ Finset.range N, |x| ^ k / k.factorial := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [abs_div, abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k.factorial : ℝ))]
    _ ≤ Real.exp |x| := sum_le_hasSum (Finset.range N) (fun k _ => by positivity) hsum

/-- **Single-site moment positivity with an external field** (GJ §4.7 Griffiths-I,
`c₁, c₂ ≥ 0`): for `A > 0`,
`0 ≤ ∫_{ℝ²} tᵃqᵇ·exp(c₁t + c₂q)·exp(−A(t²+q²)² − σ(t²+q²))`. Expanding the field
exponentials by `expTrunc` gives finite sums of non-negative-coefficient moments,
each `≥ 0` by `singleSpinMoment_nonneg`; dominated convergence (with the linear
field absorbed into the quadratic via `|t| ≤ (1+t²)/2`) passes to the limit. -/
theorem singleSpinMoment_field_nonneg {A σ c₁ c₂ : ℝ} (hA : 0 < A)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (a b : ℕ) :
    0 ≤ ∫ ξ : ℝ × ℝ, ξ.1 ^ a * ξ.2 ^ b * Real.exp (c₁ * ξ.1 + c₂ * ξ.2)
      * singleSpinDensity A σ ξ := by
  classical
  set F : ℕ → ℝ × ℝ → ℝ := fun N ξ =>
    ξ.1 ^ a * ξ.2 ^ b * expTrunc N (c₁ * ξ.1) * expTrunc N (c₂ * ξ.2)
      * singleSpinDensity A σ ξ with hF
  -- Each truncated integral is non-negative (finite expansion into single-site moments).
  have hFnn : ∀ N : ℕ, 0 ≤ ∫ ξ, F N ξ := by
    intro N
    have hFeq : ∀ ξ : ℝ × ℝ, F N ξ
        = ∑ m ∈ Finset.range N, ∑ l ∈ Finset.range N,
            (c₁ ^ m / m.factorial * (c₂ ^ l / l.factorial)) *
              (ξ.1 ^ (a + m) * ξ.2 ^ (b + l) * singleSpinDensity A σ ξ) := by
      intro ξ
      have hrw : F N ξ
          = (ξ.1 ^ a * ξ.2 ^ b * singleSpinDensity A σ ξ) *
              ((∑ m ∈ Finset.range N, (c₁ * ξ.1) ^ m / m.factorial) *
               (∑ l ∈ Finset.range N, (c₂ * ξ.2) ^ l / l.factorial)) := by
        simp only [hF, expTrunc]; ring
      rw [hrw, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [mul_pow, mul_pow, pow_add, pow_add]; ring
    have hint : ∀ m l : ℕ, Integrable (fun ξ : ℝ × ℝ =>
        (c₁ ^ m / m.factorial * (c₂ ^ l / l.factorial)) *
          (ξ.1 ^ (a + m) * ξ.2 ^ (b + l) * singleSpinDensity A σ ξ)) :=
      fun m l => (integrable_pow_mul_singleSpinDensity hA (a + m) (b + l)).const_mul _
    calc (∫ ξ, F N ξ)
        = ∑ m ∈ Finset.range N, ∑ l ∈ Finset.range N,
            (c₁ ^ m / m.factorial * (c₂ ^ l / l.factorial)) *
              ∫ ξ : ℝ × ℝ, ξ.1 ^ (a + m) * ξ.2 ^ (b + l) * singleSpinDensity A σ ξ := by
          simp_rw [hFeq]
          rw [integral_finset_sum _ (fun m _ => integrable_finset_sum _ (fun l _ => hint m l))]
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [integral_finset_sum _ (fun l _ => hint m l)]
          exact Finset.sum_congr rfl (fun l _ => integral_const_mul _ _)
      _ ≥ 0 := by
          refine Finset.sum_nonneg (fun m _ => Finset.sum_nonneg (fun l _ => ?_))
          exact mul_nonneg (by positivity) (singleSpinMoment_nonneg hA _ _)
  -- Dominated convergence to the field integrand.
  set d : ℝ := max |c₁| |c₂| / 2 with hd
  have hbnd_int : Integrable (fun ξ : ℝ × ℝ =>
      Real.exp ((|c₁| + |c₂|) / 2) *
        ‖ξ.1 ^ a * ξ.2 ^ b * singleSpinDensity A (σ - d) ξ‖) :=
    ((integrable_pow_mul_singleSpinDensity (A := A) (σ := σ - d) hA a b).norm).const_mul _
  have hlim : Filter.Tendsto (fun N => ∫ ξ, F N ξ) Filter.atTop
      (nhds (∫ ξ : ℝ × ℝ, ξ.1 ^ a * ξ.2 ^ b * Real.exp (c₁ * ξ.1) * Real.exp (c₂ * ξ.2)
        * singleSpinDensity A σ ξ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun ξ => Real.exp ((|c₁| + |c₂|) / 2) *
        ‖ξ.1 ^ a * ξ.2 ^ b * singleSpinDensity A (σ - d) ξ‖)
      (fun N => ?_) hbnd_int (fun N => ?_) ?_
    · have hc : Continuous (F N) := by
        simp only [hF]
        exact ((((continuous_fst.pow a).mul (continuous_snd.pow b)).mul
          ((continuous_expTrunc N).comp (continuous_const.mul continuous_fst))).mul
          ((continuous_expTrunc N).comp (continuous_const.mul continuous_snd))).mul
            (continuous_singleSpinDensity A σ)
      exact hc.aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ξ => ?_)
      simp only []
      have hdens : (0:ℝ) < singleSpinDensity A σ ξ := Real.exp_pos _
      have hdensd : (0:ℝ) < singleSpinDensity A (σ - d) ξ := Real.exp_pos _
      have hnormF : ‖F N ξ‖
          = |ξ.1| ^ a * |ξ.2| ^ b * |expTrunc N (c₁ * ξ.1)| * |expTrunc N (c₂ * ξ.2)|
            * singleSpinDensity A σ ξ := by
        simp only [hF, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hdens]
      rw [hnormF, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow,
        abs_of_pos hdensd]
      have hexple : |expTrunc N (c₁ * ξ.1)| * |expTrunc N (c₂ * ξ.2)|
          ≤ Real.exp ((|c₁| + |c₂|) / 2) * Real.exp (d * (ξ.1 ^ 2 + ξ.2 ^ 2)) := by
        have h1 : |expTrunc N (c₁ * ξ.1)| ≤ Real.exp |c₁ * ξ.1| := abs_expTrunc_le_exp_abs _ _
        have h2 : |expTrunc N (c₂ * ξ.2)| ≤ Real.exp |c₂ * ξ.2| := abs_expTrunc_le_exp_abs _ _
        have hle : |c₁ * ξ.1| + |c₂ * ξ.2|
            ≤ (|c₁| + |c₂|) / 2 + d * (ξ.1 ^ 2 + ξ.2 ^ 2) := by
          rw [abs_mul, abs_mul]
          have ht : |ξ.1| ≤ (1 + ξ.1 ^ 2) / 2 := by
            nlinarith [sq_nonneg (|ξ.1| - 1), sq_abs ξ.1, abs_nonneg ξ.1]
          have hq : |ξ.2| ≤ (1 + ξ.2 ^ 2) / 2 := by
            nlinarith [sq_nonneg (|ξ.2| - 1), sq_abs ξ.2, abs_nonneg ξ.2]
          have hd1 : |c₁| ≤ 2 * d := by rw [hd]; have := le_max_left |c₁| |c₂|; linarith
          have hd2 : |c₂| ≤ 2 * d := by rw [hd]; have := le_max_right |c₁| |c₂|; linarith
          nlinarith [abs_nonneg c₁, abs_nonneg c₂, abs_nonneg ξ.1, abs_nonneg ξ.2,
            mul_le_mul_of_nonneg_left ht (abs_nonneg c₁),
            mul_le_mul_of_nonneg_left hq (abs_nonneg c₂), sq_nonneg ξ.1, sq_nonneg ξ.2]
        calc |expTrunc N (c₁ * ξ.1)| * |expTrunc N (c₂ * ξ.2)|
            ≤ Real.exp |c₁ * ξ.1| * Real.exp |c₂ * ξ.2| :=
              mul_le_mul h1 h2 (abs_nonneg _) (Real.exp_pos _).le
          _ = Real.exp (|c₁ * ξ.1| + |c₂ * ξ.2|) := (Real.exp_add _ _).symm
          _ ≤ Real.exp ((|c₁| + |c₂|) / 2 + d * (ξ.1 ^ 2 + ξ.2 ^ 2)) := Real.exp_le_exp.mpr hle
          _ = Real.exp ((|c₁| + |c₂|) / 2) * Real.exp (d * (ξ.1 ^ 2 + ξ.2 ^ 2)) := Real.exp_add _ _
      have hdens_eq : singleSpinDensity A (σ - d) ξ
          = Real.exp (d * (ξ.1 ^ 2 + ξ.2 ^ 2)) * singleSpinDensity A σ ξ := by
        simp only [singleSpinDensity, ← Real.exp_add]; congr 1; ring
      rw [hdens_eq]
      calc |ξ.1| ^ a * |ξ.2| ^ b * |expTrunc N (c₁ * ξ.1)| * |expTrunc N (c₂ * ξ.2)|
              * singleSpinDensity A σ ξ
          = (|ξ.1| ^ a * |ξ.2| ^ b * singleSpinDensity A σ ξ)
              * (|expTrunc N (c₁ * ξ.1)| * |expTrunc N (c₂ * ξ.2)|) := by ring
        _ ≤ (|ξ.1| ^ a * |ξ.2| ^ b * singleSpinDensity A σ ξ)
              * (Real.exp ((|c₁| + |c₂|) / 2) * Real.exp (d * (ξ.1 ^ 2 + ξ.2 ^ 2))) :=
            mul_le_mul_of_nonneg_left hexple (by positivity)
        _ = Real.exp ((|c₁| + |c₂|) / 2)
              * (|ξ.1| ^ a * |ξ.2| ^ b * (Real.exp (d * (ξ.1 ^ 2 + ξ.2 ^ 2))
                * singleSpinDensity A σ ξ)) := by ring
    · refine Filter.Eventually.of_forall (fun ξ => ?_)
      have htarget : ξ.1 ^ a * ξ.2 ^ b * Real.exp (c₁ * ξ.1) * Real.exp (c₂ * ξ.2)
          * singleSpinDensity A σ ξ
          = (ξ.1 ^ a * ξ.2 ^ b * singleSpinDensity A σ ξ)
            * (Real.exp (c₁ * ξ.1) * Real.exp (c₂ * ξ.2)) := by ring
      rw [htarget]
      have hFξ : (fun N => F N ξ)
          = fun N => (ξ.1 ^ a * ξ.2 ^ b * singleSpinDensity A σ ξ)
            * (expTrunc N (c₁ * ξ.1) * expTrunc N (c₂ * ξ.2)) := by
        funext N; simp only [hF]; ring
      rw [hFξ]
      exact tendsto_const_nhds.mul ((tendsto_expTrunc _).mul (tendsto_expTrunc _))
  -- Conclude: limit of non-negatives is non-negative; rewrite the field exponential.
  have hgoal : (∫ ξ : ℝ × ℝ, ξ.1 ^ a * ξ.2 ^ b * Real.exp (c₁ * ξ.1 + c₂ * ξ.2)
      * singleSpinDensity A σ ξ)
      = ∫ ξ : ℝ × ℝ, ξ.1 ^ a * ξ.2 ^ b * Real.exp (c₁ * ξ.1) * Real.exp (c₂ * ξ.2)
        * singleSpinDensity A σ ξ := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
    simp only []
    rw [Real.exp_add]; ring
  rw [hgoal]
  exact ge_of_tendsto' hlim hFnn

end IsingModel.ContinuousSpin
