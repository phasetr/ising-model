import IsingModel.ContinuousSpin.TwoComponentGriffithsI
import IsingModel.ContinuousSpin.TwoComponent

/-!
# Foundations for the second/third Griffiths inequalities (GJ Theorem 4.7.1)

Foundational integrability lemmas for the duplicate-variable proof of the
second and third inequalities of Glimm–Jaffe Theorem 4.7.1 (4.7.6)–(4.7.8),
pp. 70–71.  This file builds the full-line quartic integrability used by the
rotated single-site doubled density.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.7, Theorem 4.7.1, pp. 70–71
-/

namespace IsingModel.ContinuousSpin

open Real MeasureTheory Set

/-- **Full-line integrability of `xᵃ·exp(b·x² − A·x⁴)`** for `A > 0`: the quartic
term dominates, so the polynomial-weighted super-quartic density is integrable
over all of `ℝ` (not just `(0,∞)`).  Proved by splitting `ℝ = Iic 0 ∪ Ioi 0` and
reflecting the negative half onto `(0,∞)` via the measure-preserving negation. -/
theorem integrable_pow_mul_exp_quad_quartic {A b : ℝ} (hA : 0 < A) (a : ℕ) :
    Integrable (fun x : ℝ => x ^ a * Real.exp (b * x ^ 2 - A * x ^ 4)) := by
  -- An even, non-negative dominating function `g x = |x|ᵃ·exp(−(A/2)·x⁴)`.
  have hA2 : (0 : ℝ) < A / 2 := by linarith
  have hmeas : MeasurableEmbedding (Neg.neg : ℝ → ℝ) :=
    (Homeomorph.neg ℝ).measurableEmbedding
  have hmp : MeasurePreserving (Neg.neg : ℝ → ℝ) volume volume := Measure.measurePreserving_neg _
  have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Ioi 0 = Iio 0 := by ext x; simp [Set.mem_Iio]
  -- `g` is integrable on `(0,∞)` (`|x| = x` there) and, by evenness, on `(-∞,0)`.
  have hgIoi : IntegrableOn (fun x : ℝ => |x| ^ a * Real.exp (-(A / 2) * x ^ 4)) (Ioi 0) := by
    refine IntegrableOn.congr_fun (integrableOn_pow_quad_quartic (A := A / 2) (b := 0) hA2 a)
      (fun x hx => ?_) measurableSet_Ioi
    rw [abs_of_pos hx]; ring_nf
  have hgIio : IntegrableOn (fun x : ℝ => |x| ^ a * Real.exp (-(A / 2) * x ^ 4)) (Iio 0) := by
    have h0 := (hmp.integrableOn_comp_preimage hmeas
      (f := fun x : ℝ => |x| ^ a * Real.exp (-(A / 2) * x ^ 4)) (s := Ioi 0)).mpr hgIoi
    rw [hpre] at h0
    refine IntegrableOn.congr_fun h0 (fun x _ => ?_) measurableSet_Iio
    simp only [Function.comp_apply, abs_neg, show ((-x) ^ 4) = x ^ 4 from by ring]
  have hg : Integrable (fun x : ℝ => |x| ^ a * Real.exp (-(A / 2) * x ^ 4)) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    exact ⟨(integrableOn_Iic_iff_integrableOn_Iio).mpr hgIio, hgIoi⟩
  -- `f` is dominated by `exp(b²/(2A))·g`.
  refine ((hg.const_mul (Real.exp (b ^ 2 / (2 * A)))).mono'
    (((continuous_id.pow a).mul (by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_))
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  have hexp : b * x ^ 2 - A * x ^ 4 ≤ b ^ 2 / (2 * A) + (-(A / 2) * x ^ 4) := by
    have hid : b * x ^ 2 - A * x ^ 4
        = b ^ 2 / (2 * A) - (A / 2) * x ^ 4 - (A * x ^ 2 - b) ^ 2 / (2 * A) := by
      field_simp; ring
    have : 0 ≤ (A * x ^ 2 - b) ^ 2 / (2 * A) := div_nonneg (sq_nonneg _) (by linarith)
    rw [hid]; linarith
  calc |x| ^ a * Real.exp (b * x ^ 2 - A * x ^ 4)
      ≤ |x| ^ a * Real.exp (b ^ 2 / (2 * A) + (-(A / 2) * x ^ 4)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = Real.exp (b ^ 2 / (2 * A)) * (|x| ^ a * Real.exp (-(A / 2) * x ^ 4)) := by
        rw [Real.exp_add]; ring

/-- Absolute version: `|x|ᵃ·exp(b·x² − A·x⁴)` is integrable over `ℝ` for `A > 0`. -/
theorem integrable_abs_pow_mul_exp_quad_quartic {A b : ℝ} (hA : 0 < A) (a : ℕ) :
    Integrable (fun x : ℝ => |x| ^ a * Real.exp (b * x ^ 2 - A * x ^ 4)) := by
  refine (integrable_pow_mul_exp_quad_quartic (b := b) hA a).norm.congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]

/-! ## The rotated single-site doubled density (4 variables `α,β,γ,δ`) -/

/-- The rotated single-site doubled density `exp(−twoCompEvenPart + 4A·αβγδ)`,
with the four rotated variables `(α,β,γ,δ) = (p 0, p 1, p 2, p 3)`. -/
noncomputable def rotSiteDensity (A σ : ℝ) (p : Fin 4 → ℝ) : ℝ :=
  Real.exp (-twoCompEvenPart A σ (p 0) (p 1) (p 2) (p 3) + 4 * A * (p 0 * p 1 * p 2 * p 3))

/-- The rotated single-site density is positive. -/
theorem rotSiteDensity_pos (A σ : ℝ) (p : Fin 4 → ℝ) : 0 < rotSiteDensity A σ p :=
  Real.exp_pos _

/-- The rotated single-site density is continuous. -/
theorem continuous_rotSiteDensity (A σ : ℝ) : Continuous (rotSiteDensity A σ) := by
  unfold rotSiteDensity twoCompEvenPart; fun_prop

/-- **Uniform exponent bound for the rotated doubled density** (AM-GM):
`−twoCompEvenPart + 4A·αβγδ ≤ ∑ⱼ (−σ·xⱼ² − (A/2)·xⱼ⁴)`.  The only positive cross
term `4A·αβγδ ≤ 2A(α²β²+γ²δ²)` is absorbed by the negative `−3A(α²β²+γ²δ²)`. -/
theorem rotExponent_le (A σ α β γ δ : ℝ) (hA : 0 ≤ A) :
    -twoCompEvenPart A σ α β γ δ + 4 * A * (α * β * γ * δ)
      ≤ (-σ * α ^ 2 - (A / 2) * α ^ 4) + (-σ * β ^ 2 - (A / 2) * β ^ 4)
          + (-σ * γ ^ 2 - (A / 2) * γ ^ 4) + (-σ * δ ^ 2 - (A / 2) * δ ^ 4) := by
  simp only [twoCompEvenPart]
  nlinarith [mul_nonneg hA (sq_nonneg (α * β - γ * δ)), mul_nonneg hA (sq_nonneg (α * γ)),
    mul_nonneg hA (sq_nonneg (α * δ)), mul_nonneg hA (sq_nonneg (β * γ)),
    mul_nonneg hA (sq_nonneg (β * δ)), mul_nonneg hA (sq_nonneg (α * β + γ * δ))]

/-- **4D integrability of the monomial-weighted rotated doubled density**:
`p ↦ (∏ⱼ pⱼ^{eⱼ})·rotSiteDensity A σ p` is integrable over `(Fin 4 → ℝ)` for
`A > 0`.  Dominated by the product `∏ⱼ |pⱼ|^{eⱼ}·exp(−σ·pⱼ² − (A/2)·pⱼ⁴)` via the
exponent bound `rotExponent_le`, integrable by `Integrable.fintype_prod`. -/
theorem integrable_monomial_mul_rotSiteDensity {A σ : ℝ} (hA : 0 < A) (e : Fin 4 → ℕ) :
    Integrable (fun p : Fin 4 → ℝ => (∏ j, p j ^ e j) * rotSiteDensity A σ p) := by
  have hdom : Integrable (fun p : Fin 4 → ℝ =>
      ∏ j, (|p j| ^ e j * Real.exp (-σ * p j ^ 2 - (A / 2) * p j ^ 4))) := by
    rw [volume_pi]
    exact Integrable.fintype_prod fun j =>
      integrable_abs_pow_mul_exp_quad_quartic (by linarith) (e j)
  refine hdom.mono'
    (((continuous_finset_prod _ fun j _ => (continuous_apply j).pow (e j)).mul
      (continuous_rotSiteDensity A σ)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (rotSiteDensity_pos A σ p), Finset.abs_prod]
  have hprod_eq : (∏ j, |p j ^ e j|)
      = ∏ j, |p j| ^ e j := by
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [abs_pow]
  rw [hprod_eq]
  have hexp : rotSiteDensity A σ p
      ≤ ∏ j, Real.exp (-σ * p j ^ 2 - (A / 2) * p j ^ 4) := by
    rw [rotSiteDensity, ← Real.exp_sum, Fin.sum_univ_four]
    exact Real.exp_le_exp.mpr (rotExponent_le A σ (p 0) (p 1) (p 2) (p 3) hA.le)
  calc (∏ j, |p j| ^ e j) * rotSiteDensity A σ p
      ≤ (∏ j, |p j| ^ e j) * ∏ j, Real.exp (-σ * p j ^ 2 - (A / 2) * p j ^ 4) :=
        mul_le_mul_of_nonneg_left hexp (Finset.prod_nonneg fun j _ => by positivity)
    _ = ∏ j, (|p j| ^ e j * Real.exp (-σ * p j ^ 2 - (A / 2) * p j ^ 4)) := by
        rw [← Finset.prod_mul_distrib]

/-- **4D integrability of the monomial-weighted rotated doubled density with an
external field** `exp(c_α·α + c_γ·γ)` (the field couples to `α = p 0` and
`γ = p 2`).  The linear field is absorbed into the quadratic part via
`|t| ≤ (1+t²)/2`, raising the per-coordinate quadratic coefficient from `−σ` to
`d − σ` (`d = max|c_α||c_γ|/2`); the result remains a product of integrable
super-quartic factors. -/
theorem integrable_monomial_mul_field_rotSiteDensity {A σ cα cγ : ℝ} (hA : 0 < A)
    (e : Fin 4 → ℕ) :
    Integrable (fun p : Fin 4 → ℝ =>
      (∏ j, p j ^ e j) * Real.exp (cα * p 0 + cγ * p 2) * rotSiteDensity A σ p) := by
  set d : ℝ := max |cα| |cγ| / 2 with hd
  have hdom : Integrable (fun p : Fin 4 → ℝ =>
      Real.exp ((|cα| + |cγ|) / 2)
        * ∏ j, (|p j| ^ e j * Real.exp ((d - σ) * p j ^ 2 - (A / 2) * p j ^ 4))) := by
    refine Integrable.const_mul ?_ _
    rw [volume_pi]
    exact Integrable.fintype_prod fun j =>
      integrable_abs_pow_mul_exp_quad_quartic (b := d - σ) (by linarith) (e j)
  refine hdom.mono'
    ((((continuous_finset_prod _ fun j _ => (continuous_apply j).pow (e j)).mul
      (by fun_prop)).mul (continuous_rotSiteDensity A σ)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (rotSiteDensity_pos A σ p),
    abs_of_pos (Real.exp_pos _), Finset.abs_prod]
  have hprod_eq : (∏ j, |p j ^ e j|) = ∏ j, |p j| ^ e j :=
    Finset.prod_congr rfl fun j _ => abs_pow _ _
  rw [hprod_eq]
  -- Combined exponent bound: field + density exponent ≤ constant + per-site form.
  have hdnn : (0 : ℝ) ≤ d := by rw [hd]; positivity
  have hcomb : cα * p 0 + cγ * p 2 + (-twoCompEvenPart A σ (p 0) (p 1) (p 2) (p 3)
        + 4 * A * (p 0 * p 1 * p 2 * p 3))
      ≤ (|cα| + |cγ|) / 2 + ∑ j, ((d - σ) * p j ^ 2 - (A / 2) * p j ^ 4) := by
    have hd1 : |cα| ≤ 2 * d := by rw [hd]; have := le_max_left |cα| |cγ|; linarith
    have hd2 : |cγ| ≤ 2 * d := by rw [hd]; have := le_max_right |cα| |cγ|; linarith
    have hfα : cα * p 0 ≤ |cα| / 2 + d * p 0 ^ 2 := by
      have ht : |p 0| ≤ (1 + p 0 ^ 2) / 2 := by nlinarith [sq_nonneg (|p 0| - 1), sq_abs (p 0)]
      have h0 : cα * p 0 ≤ |cα| * |p 0| := (le_abs_self _).trans (by rw [abs_mul])
      nlinarith [h0, mul_le_mul_of_nonneg_left ht (abs_nonneg cα),
        mul_nonneg (sq_nonneg (p 0)) (by linarith [hd1] : (0 : ℝ) ≤ 2 * d - |cα|)]
    have hfγ : cγ * p 2 ≤ |cγ| / 2 + d * p 2 ^ 2 := by
      have ht : |p 2| ≤ (1 + p 2 ^ 2) / 2 := by nlinarith [sq_nonneg (|p 2| - 1), sq_abs (p 2)]
      have h0 : cγ * p 2 ≤ |cγ| * |p 2| := (le_abs_self _).trans (by rw [abs_mul])
      nlinarith [h0, mul_le_mul_of_nonneg_left ht (abs_nonneg cγ),
        mul_nonneg (sq_nonneg (p 2)) (by linarith [hd2] : (0 : ℝ) ≤ 2 * d - |cγ|)]
    have hrot := rotExponent_le A σ (p 0) (p 1) (p 2) (p 3) hA.le
    rw [Fin.sum_univ_four]
    nlinarith [hfα, hfγ, hrot, mul_nonneg hdnn (sq_nonneg (p 1)),
      mul_nonneg hdnn (sq_nonneg (p 3))]
  rw [mul_assoc, rotSiteDensity, ← Real.exp_add]
  calc (∏ j, |p j| ^ e j) * Real.exp (cα * p 0 + cγ * p 2
        + (-twoCompEvenPart A σ (p 0) (p 1) (p 2) (p 3) + 4 * A * (p 0 * p 1 * p 2 * p 3)))
      ≤ (∏ j, |p j| ^ e j) * Real.exp ((|cα| + |cγ|) / 2
          + ∑ j, ((d - σ) * p j ^ 2 - (A / 2) * p j ^ 4)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcomb)
          (Finset.prod_nonneg fun j _ => by positivity)
    _ = Real.exp ((|cα| + |cγ|) / 2)
          * ∏ j, (|p j| ^ e j * Real.exp ((d - σ) * p j ^ 2 - (A / 2) * p j ^ 4)) := by
        rw [Real.exp_add, Real.exp_sum, Finset.prod_mul_distrib]; ring

end IsingModel.ContinuousSpin
