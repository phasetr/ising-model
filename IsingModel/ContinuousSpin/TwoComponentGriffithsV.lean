import IsingModel.ContinuousSpin.TwoComponentGriffithsIV
import IsingModel.ContinuousSpin.TwoComponentSystem
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The four-variable doubled-rotated cone (GJ Theorem 4.7.1, second/third)

The multi-site non-negative-coefficient polynomial cone for the *doubled rotated*
measure underlying the second and third inequalities of GJ Theorem 4.7.1
(4.7.6)–(4.7.8), pp. 70–71.  This is the four-variable analogue of the cone in
`TwoComponentGriffithsI.lean`: a configuration assigns to each site `i` the four
rotated coordinates `(α,β,γ,δ) = cfg i : Fin 4 → ℝ`, the per-site weight is
`siteWeight4 A σ c_α c_γ q = exp(c_α·q₀ + c_γ·q₂)·rotSiteDensity A σ q`, and the
interaction is the ferromagnetic `∑_e (αᵢαⱼ + βᵢβⱼ + γᵢγⱼ + δᵢδⱼ)`.

The integral of a non-negative-coefficient polynomial against the product weight
factorises (`eval_eq'`, `Fintype.prod_prod_type`,
`integral_fintype_prod_volume_eq_prod`) into single-site field moments
`twoComp_single_site_field_prod_nonneg`, hence `≥ 0`.  Truncating the interaction
exponential and applying dominated convergence gives the doubled rotated
non-negativity used by the duplicate-variable argument.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.7, Theorem 4.7.1, pp. 70–71
-/

namespace IsingModel.ContinuousSpin

open Real MeasureTheory MvPolynomial
open scoped BigOperators

variable {ι : Type*}

/-! ## The doubled-rotated per-site weight -/

/-- The doubled-rotated per-site weight `exp(c_α·q₀ + c_γ·q₂)·rotSiteDensity A σ q`. -/
noncomputable def siteWeight4 (A σ cα cγ : ℝ) (q : Fin 4 → ℝ) : ℝ :=
  Real.exp (cα * q 0 + cγ * q 2) * rotSiteDensity A σ q

/-- The doubled-rotated per-site weight is positive. -/
theorem siteWeight4_pos (A σ cα cγ : ℝ) (q : Fin 4 → ℝ) : 0 < siteWeight4 A σ cα cγ q :=
  mul_pos (Real.exp_pos _) (rotSiteDensity_pos A σ q)

/-- The doubled-rotated per-site weight is continuous. -/
theorem continuous_siteWeight4 (A σ cα cγ : ℝ) : Continuous (siteWeight4 A σ cα cγ) := by
  unfold siteWeight4
  exact (Real.continuous_exp.comp (by fun_prop)).mul (continuous_rotSiteDensity A σ)

/-- Integrability of the monomial-weighted doubled-rotated per-site weight. -/
theorem integrable_monomial_mul_siteWeight4 {A σ cα cγ : ℝ} (hA : 0 < A) (e : Fin 4 → ℕ) :
    Integrable (fun q : Fin 4 → ℝ => (∏ j, q j ^ e j) * siteWeight4 A σ cα cγ q) := by
  have heq : ∀ q : Fin 4 → ℝ, (∏ j, q j ^ e j) * siteWeight4 A σ cα cγ q
      = (∏ j, q j ^ e j) * Real.exp (cα * q 0 + cγ * q 2) * rotSiteDensity A σ q := by
    intro q; rw [siteWeight4]; ring
  simp_rw [heq]
  exact integrable_monomial_mul_field_rotSiteDensity hA e

/-- Single-site moment non-negativity for the doubled-rotated per-site weight. -/
theorem siteWeight4_moment_nonneg {A σ cα cγ : ℝ} (hA : 0 < A) (hcα : 0 ≤ cα) (hcγ : 0 ≤ cγ)
    (e : Fin 4 → ℕ) :
    0 ≤ ∫ q : Fin 4 → ℝ, (∏ j, q j ^ e j) * siteWeight4 A σ cα cγ q := by
  have heq : ∀ q : Fin 4 → ℝ, (∏ j, q j ^ e j) * siteWeight4 A σ cα cγ q
      = (∏ j, q j ^ e j) * Real.exp (cα * q 0 + cγ * q 2) * rotSiteDensity A σ q := by
    intro q; rw [siteWeight4]; ring
  simp_rw [heq]
  exact twoComp_single_site_field_prod_nonneg hA hcα hcγ e

/-! ## The non-negative-coefficient cone over `ι × Fin 4` -/

/-- The doubled-rotated valuation: variable `(i, j)` evaluates to `cfg i j`. -/
noncomputable def dSpinVal (cfg : ι → Fin 4 → ℝ) : ι × Fin 4 → ℝ := fun v => cfg v.1 v.2

/-- Evaluation of a doubled-rotated polynomial at a configuration. -/
noncomputable def dSpinEval (p : MvPolynomial (ι × Fin 4) ℝ) (cfg : ι → Fin 4 → ℝ) : ℝ :=
  MvPolynomial.eval (dSpinVal cfg) p

/-- A polynomial over `ι × Fin 4` has non-negative coefficients. -/
def NNCoeffs (p : MvPolynomial (ι × Fin 4) ℝ) : Prop := ∀ m, 0 ≤ MvPolynomial.coeff m p

theorem NNCoeffs.zero : NNCoeffs (0 : MvPolynomial (ι × Fin 4) ℝ) := fun m => by simp

theorem NNCoeffs.one : NNCoeffs (1 : MvPolynomial (ι × Fin 4) ℝ) := fun m => by
  classical rw [coeff_one]; split <;> norm_num

theorem NNCoeffs.X (v : ι × Fin 4) : NNCoeffs (MvPolynomial.X v : MvPolynomial (ι × Fin 4) ℝ) :=
  fun m => by classical rw [coeff_X']; split <;> norm_num

theorem NNCoeffs.C {c : ℝ} (hc : 0 ≤ c) :
    NNCoeffs (MvPolynomial.C c : MvPolynomial (ι × Fin 4) ℝ) := fun m => by
  classical rw [coeff_C]; split <;> [exact hc; exact le_refl 0]

theorem NNCoeffs.add {p q : MvPolynomial (ι × Fin 4) ℝ}
    (hp : NNCoeffs p) (hq : NNCoeffs q) : NNCoeffs (p + q) := fun m => by
  rw [coeff_add]; exact add_nonneg (hp m) (hq m)

theorem NNCoeffs.mul {p q : MvPolynomial (ι × Fin 4) ℝ}
    (hp : NNCoeffs p) (hq : NNCoeffs q) : NNCoeffs (p * q) := fun m => by
  classical rw [coeff_mul]; exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)

theorem NNCoeffs.sum {α : Type*} {s : Finset α} {f : α → MvPolynomial (ι × Fin 4) ℝ}
    (h : ∀ a ∈ s, NNCoeffs (f a)) : NNCoeffs (∑ a ∈ s, f a) :=
  Finset.sum_induction f NNCoeffs (fun _ _ => NNCoeffs.add) NNCoeffs.zero h

theorem NNCoeffs.prod {α : Type*} {s : Finset α} {f : α → MvPolynomial (ι × Fin 4) ℝ}
    (h : ∀ a ∈ s, NNCoeffs (f a)) : NNCoeffs (∏ a ∈ s, f a) :=
  Finset.prod_induction f NNCoeffs (fun _ _ => NNCoeffs.mul) NNCoeffs.one h

theorem NNCoeffs.pow {p : MvPolynomial (ι × Fin 4) ℝ} (hp : NNCoeffs p) :
    ∀ k : ℕ, NNCoeffs (p ^ k)
  | 0 => by simpa using NNCoeffs.one
  | k + 1 => by rw [pow_succ]; exact (NNCoeffs.pow hp k).mul hp

/-! ## The cone integral is non-negative -/

/-- Integrability of a site-product over the doubled-rotated configuration. -/
theorem integrable_dmonomial_mul_siteWeight4Prod [Fintype ι] {A σ cα cγ : ℝ} (hA : 0 < A)
    (a : ι → Fin 4 → ℕ) :
    Integrable (fun cfg : ι → Fin 4 → ℝ =>
      ∏ i, ((∏ j, cfg i j ^ a i j) * siteWeight4 A σ cα cγ (cfg i))) := by
  rw [volume_pi]
  exact Integrable.fintype_prod fun i => integrable_monomial_mul_siteWeight4 hA (a i)

/-- The integral of a site-product factorises into single-site moments. -/
theorem integral_dmonomial_mul_siteWeight4Prod [Fintype ι] {A σ cα cγ : ℝ} (a : ι → Fin 4 → ℕ) :
    ∫ cfg : ι → Fin 4 → ℝ, ∏ i, ((∏ j, cfg i j ^ a i j) * siteWeight4 A σ cα cγ (cfg i))
      = ∏ i, ∫ q : Fin 4 → ℝ, (∏ j, q j ^ a i j) * siteWeight4 A σ cα cγ q :=
  integral_fintype_prod_volume_eq_prod
    (fun i q => (∏ j, q j ^ a i j) * siteWeight4 A σ cα cγ q)

/-- **The integral of a non-negative-coefficient doubled-rotated polynomial against
the product weight is non-negative.** -/
theorem dSpinEval_integral_nonneg [Fintype ι] {A σ cα cγ : ℝ} (hA : 0 < A) (hcα : 0 ≤ cα)
    (hcγ : 0 ≤ cγ)
    {p : MvPolynomial (ι × Fin 4) ℝ} (hp : NNCoeffs p) :
    0 ≤ ∫ cfg : ι → Fin 4 → ℝ, dSpinEval p cfg * ∏ i, siteWeight4 A σ cα cγ (cfg i) := by
  classical
  have hpt : ∀ cfg : ι → Fin 4 → ℝ, dSpinEval p cfg * ∏ i, siteWeight4 A σ cα cγ (cfg i)
      = ∑ d ∈ p.support, p.coeff d *
          ∏ i, ((∏ j, cfg i j ^ d (i, j)) * siteWeight4 A σ cα cγ (cfg i)) := by
    intro cfg
    rw [dSpinEval, eval_eq', Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [mul_assoc]
    congr 1
    rw [Fintype.prod_prod_type (f := fun v => dSpinVal cfg v ^ d v),
      ← Finset.prod_mul_distrib]
    simp only [dSpinVal]
  simp_rw [hpt]
  have hintegr : ∀ d : (ι × Fin 4) →₀ ℕ, Integrable (fun cfg : ι → Fin 4 → ℝ =>
      p.coeff d * ∏ i, ((∏ j, cfg i j ^ d (i, j)) * siteWeight4 A σ cα cγ (cfg i))) :=
    fun d => (integrable_dmonomial_mul_siteWeight4Prod hA (fun i j => d (i, j))).const_mul _
  rw [integral_finset_sum _ (fun d _ => hintegr d)]
  refine Finset.sum_nonneg fun d _ => ?_
  rw [integral_const_mul, integral_dmonomial_mul_siteWeight4Prod]
  exact mul_nonneg (hp d) (Finset.prod_nonneg fun i _ => siteWeight4_moment_nonneg hA hcα hcγ _)

end IsingModel.ContinuousSpin
