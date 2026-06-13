import IsingModel.ContinuousSpin.TwoComponentMultiIntegrable
import IsingModel.ContinuousSpin.TwoComponentGriffiths
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The first Griffiths inequality for two-component spins (GJ Theorem 4.7.1)

The first inequality of Glimm–Jaffe Theorem 4.7.1 (p. 70) states that for the
ferromagnetic two-component (planar rotator) Gibbs measure with a non-negative
external field, every monomial correlation is non-negative:
`⟨∏_{i∈A} tᵢ · ∏_{j∈B} qⱼ⟩ ≥ 0`.

## Strategy

The unnormalised correlation is
`∫ (∏_{i∈A} tᵢ ∏_{j∈B} qⱼ) · exp(βJ·∑_e ξᵢ·ξⱼ) · ∏ᵢ siteWeightᵢ`,
where `siteWeightᵢ = exp(βh¹tᵢ + βh²qᵢ)·exp(−A|ξᵢ|⁴ − σ|ξᵢ|²)` is the per-site
weight (with field) and the interaction exponential couples the sites.

We replace the interaction exponential `exp(βJ·S)` by its truncation
`expTrunc N (βJ·S)`, a *polynomial* in the spins.  Crucially the truncated
integrand is `spinEval p` for a `MvPolynomial (ι ⊕ ι) ℝ` polynomial `p` with
**non-negative coefficients** (ferromagnetism `βJ ≥ 0` and `h ≥ 0` keep every
coefficient non-negative).  The integral of any non-negative-coefficient
polynomial against the product weight is a non-negative combination of products
of single-site moments `singleSpinMoment_field_nonneg`, hence `≥ 0`
(`spinEval_integral_nonneg`).  The `MvPolynomial` ring structure discharges the
otherwise painful multinomial expansion of `(∑_e ξᵢ·ξⱼ)^k`: closure under sums,
products and powers is `coeff_add` / `coeff_mul` non-negativity.

Finally dominated convergence (`tendsto_integral_of_dominated_convergence`,
with a uniform AM-GM dominator analogous to `integrable_vectorWeight`) passes to
the limit `N → ∞`, giving the non-negativity of the true correlation.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.7, Theorem 4.7.1, pp. 70–71
-/

namespace IsingModel.ContinuousSpin

open Real MeasureTheory MvPolynomial
open scoped BigOperators

variable {ι : Type*}

/-! ## The single-site weight with external field -/

/-- The single-site Gibbs weight with external field:
`siteWeight A σ c₁ c₂ ξ = exp(c₁·t + c₂·q)·exp(−A|ξ|⁴ − σ|ξ|²)`. -/
noncomputable def siteWeight (A σ c₁ c₂ : ℝ) (ξ : ℝ × ℝ) : ℝ :=
  Real.exp (c₁ * ξ.1 + c₂ * ξ.2) * singleSpinDensity A σ ξ

/-- The single-site weight is strictly positive. -/
theorem siteWeight_pos (A σ c₁ c₂ : ℝ) (ξ : ℝ × ℝ) : 0 < siteWeight A σ c₁ c₂ ξ := by
  unfold siteWeight singleSpinDensity; positivity

/-- The single-site weight is continuous. -/
theorem continuous_siteWeight (A σ c₁ c₂ : ℝ) : Continuous (siteWeight A σ c₁ c₂) :=
  ((Real.continuous_exp.comp (by fun_prop)).mul (continuous_singleSpinDensity A σ))

/-- **Integrability of the monomial-weighted single-site weight** (with field):
`ξ ↦ tᵃqᵇ·siteWeight A σ c₁ c₂ ξ` is integrable for `A > 0` and any field
couplings.  The field exponential is absorbed into the quadratic part via
`|t| ≤ (1+t²)/2`, leaving the integrable field-free monomial density of
`integrable_pow_mul_singleSpinDensity` (with `σ` shifted by `d`). -/
theorem integrable_pow_mul_siteWeight {A σ c₁ c₂ : ℝ} (hA : 0 < A) (a b : ℕ) :
    Integrable (fun ξ : ℝ × ℝ => ξ.1 ^ a * ξ.2 ^ b * siteWeight A σ c₁ c₂ ξ) := by
  set d : ℝ := max |c₁| |c₂| / 2 with hd
  have hmeas : AEStronglyMeasurable
      (fun ξ : ℝ × ℝ => ξ.1 ^ a * ξ.2 ^ b * siteWeight A σ c₁ c₂ ξ) volume :=
    (((continuous_fst.pow a).mul (continuous_snd.pow b)).mul
      (continuous_siteWeight A σ c₁ c₂)).aestronglyMeasurable
  have hbnd : Integrable (fun ξ : ℝ × ℝ =>
      Real.exp ((|c₁| + |c₂|) / 2) * ‖ξ.1 ^ a * ξ.2 ^ b * singleSpinDensity A (σ - d) ξ‖) :=
    ((integrable_pow_mul_singleSpinDensity (A := A) (σ := σ - d) hA a b).norm).const_mul _
  refine Integrable.mono' hbnd hmeas (Filter.Eventually.of_forall fun ξ => ?_)
  have hdens : (0 : ℝ) < singleSpinDensity A σ ξ := Real.exp_pos _
  have hdensd : (0 : ℝ) < singleSpinDensity A (σ - d) ξ := Real.exp_pos _
  have hnorm : ‖ξ.1 ^ a * ξ.2 ^ b * siteWeight A σ c₁ c₂ ξ‖
      = |ξ.1| ^ a * |ξ.2| ^ b * Real.exp (c₁ * ξ.1 + c₂ * ξ.2) * singleSpinDensity A σ ξ := by
    simp only [siteWeight, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hdens,
      abs_of_pos (Real.exp_pos _)]
    ring
  rw [hnorm, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos hdensd]
  have hle : c₁ * ξ.1 + c₂ * ξ.2 ≤ (|c₁| + |c₂|) / 2 + d * (ξ.1 ^ 2 + ξ.2 ^ 2) := by
    have ht : |ξ.1| ≤ (1 + ξ.1 ^ 2) / 2 := by
      nlinarith [sq_nonneg (|ξ.1| - 1), sq_abs ξ.1, abs_nonneg ξ.1]
    have hq : |ξ.2| ≤ (1 + ξ.2 ^ 2) / 2 := by
      nlinarith [sq_nonneg (|ξ.2| - 1), sq_abs ξ.2, abs_nonneg ξ.2]
    have hd1 : |c₁| ≤ 2 * d := by rw [hd]; have := le_max_left |c₁| |c₂|; linarith
    have hd2 : |c₂| ≤ 2 * d := by rw [hd]; have := le_max_right |c₁| |c₂|; linarith
    have e1 : c₁ * ξ.1 ≤ |c₁| * |ξ.1| := by
      calc c₁ * ξ.1 ≤ |c₁ * ξ.1| := le_abs_self _
        _ = |c₁| * |ξ.1| := abs_mul _ _
    have e2 : c₂ * ξ.2 ≤ |c₂| * |ξ.2| := by
      calc c₂ * ξ.2 ≤ |c₂ * ξ.2| := le_abs_self _
        _ = |c₂| * |ξ.2| := abs_mul _ _
    nlinarith [abs_nonneg c₁, abs_nonneg c₂, abs_nonneg ξ.1, abs_nonneg ξ.2,
      mul_le_mul_of_nonneg_left ht (abs_nonneg c₁),
      mul_le_mul_of_nonneg_left hq (abs_nonneg c₂), sq_nonneg ξ.1, sq_nonneg ξ.2]
  have hdens_eq : singleSpinDensity A (σ - d) ξ
      = Real.exp (d * (ξ.1 ^ 2 + ξ.2 ^ 2)) * singleSpinDensity A σ ξ := by
    simp only [singleSpinDensity, ← Real.exp_add]; congr 1; ring
  rw [hdens_eq]
  calc |ξ.1| ^ a * |ξ.2| ^ b * Real.exp (c₁ * ξ.1 + c₂ * ξ.2) * singleSpinDensity A σ ξ
      = (|ξ.1| ^ a * |ξ.2| ^ b * singleSpinDensity A σ ξ) * Real.exp (c₁ * ξ.1 + c₂ * ξ.2) := by
        ring
    _ ≤ (|ξ.1| ^ a * |ξ.2| ^ b * singleSpinDensity A σ ξ)
          * (Real.exp ((|c₁| + |c₂|) / 2) * Real.exp (d * (ξ.1 ^ 2 + ξ.2 ^ 2))) := by
        rw [← Real.exp_add]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (by positivity)
    _ = Real.exp ((|c₁| + |c₂|) / 2)
          * (|ξ.1| ^ a * |ξ.2| ^ b * (Real.exp (d * (ξ.1 ^ 2 + ξ.2 ^ 2))
            * singleSpinDensity A σ ξ)) := by ring

/-- **Integrability of the absolute monomial single-site weight**:
`ξ ↦ |t|ᵃ|q|ᵇ·siteWeight A σ c₁ c₂ ξ` is integrable for `A > 0`. -/
theorem integrable_abs_pow_mul_siteWeight {A σ c₁ c₂ : ℝ} (hA : 0 < A) (a b : ℕ) :
    Integrable (fun ξ : ℝ × ℝ => |ξ.1| ^ a * |ξ.2| ^ b * siteWeight A σ c₁ c₂ ξ) := by
  refine ((integrable_pow_mul_siteWeight (A := A) (σ := σ) (c₁ := c₁) (c₂ := c₂) hA a b).norm).congr
    (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (siteWeight_pos A σ c₁ c₂ ξ)]

/-- **Single-site moment non-negativity in `siteWeight` form**: for `A > 0` and
`c₁, c₂ ≥ 0`, `0 ≤ ∫ tᵃqᵇ·siteWeight A σ c₁ c₂`.  This is the field single-site
moment `singleSpinMoment_field_nonneg` rewritten with the packaged weight. -/
theorem siteMoment_nonneg {A σ c₁ c₂ : ℝ} (hA : 0 < A) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (a b : ℕ) :
    0 ≤ ∫ ξ : ℝ × ℝ, ξ.1 ^ a * ξ.2 ^ b * siteWeight A σ c₁ c₂ ξ := by
  have heq : (∫ ξ : ℝ × ℝ, ξ.1 ^ a * ξ.2 ^ b * siteWeight A σ c₁ c₂ ξ)
      = ∫ ξ : ℝ × ℝ, ξ.1 ^ a * ξ.2 ^ b * Real.exp (c₁ * ξ.1 + c₂ * ξ.2)
          * singleSpinDensity A σ ξ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ => by simp only [siteWeight]; ring)
  rw [heq]; exact singleSpinMoment_field_nonneg hA hc₁ hc₂ a b

/-! ## The non-negative-coefficient polynomial cone -/

/-- The spin valuation: `inl i ↦ tᵢ`, `inr i ↦ qᵢ`. -/
noncomputable def spinVal (ξ : VectorConfig ι) : ι ⊕ ι → ℝ :=
  Sum.elim (fun i => (ξ i).1) (fun i => (ξ i).2)

/-- Evaluation of a spin polynomial at a configuration. -/
noncomputable def spinEval (p : MvPolynomial (ι ⊕ ι) ℝ) (ξ : VectorConfig ι) : ℝ :=
  MvPolynomial.eval (spinVal ξ) p

/-- A polynomial has non-negative coefficients. -/
def NonnegCoeffs (p : MvPolynomial (ι ⊕ ι) ℝ) : Prop := ∀ m, 0 ≤ MvPolynomial.coeff m p

/-- The zero polynomial has non-negative coefficients. -/
theorem NonnegCoeffs.zero : NonnegCoeffs (0 : MvPolynomial (ι ⊕ ι) ℝ) := fun m => by
  simp

/-- The unit polynomial has non-negative coefficients. -/
theorem NonnegCoeffs.one : NonnegCoeffs (1 : MvPolynomial (ι ⊕ ι) ℝ) := fun m => by
  classical rw [coeff_one]; split <;> norm_num

/-- Each variable has non-negative coefficients. -/
theorem NonnegCoeffs.X (v : ι ⊕ ι) : NonnegCoeffs (MvPolynomial.X v : MvPolynomial (ι ⊕ ι) ℝ) :=
  fun m => by classical rw [coeff_X']; split <;> norm_num

/-- A non-negative constant has non-negative coefficients. -/
theorem NonnegCoeffs.C {c : ℝ} (hc : 0 ≤ c) :
    NonnegCoeffs (MvPolynomial.C c : MvPolynomial (ι ⊕ ι) ℝ) := fun m => by
  classical rw [coeff_C]; split <;> [exact hc; exact le_refl 0]

/-- Non-negative coefficients are closed under addition. -/
theorem NonnegCoeffs.add {p q : MvPolynomial (ι ⊕ ι) ℝ}
    (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) : NonnegCoeffs (p + q) := fun m => by
  rw [coeff_add]; exact add_nonneg (hp m) (hq m)

/-- Non-negative coefficients are closed under multiplication (`coeff_mul` is a
sum of products of coefficients). -/
theorem NonnegCoeffs.mul {p q : MvPolynomial (ι ⊕ ι) ℝ}
    (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) : NonnegCoeffs (p * q) := fun m => by
  classical
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)

/-- Non-negative coefficients are closed under finite sums. -/
theorem NonnegCoeffs.sum {α : Type*} {s : Finset α} {f : α → MvPolynomial (ι ⊕ ι) ℝ}
    (h : ∀ a ∈ s, NonnegCoeffs (f a)) : NonnegCoeffs (∑ a ∈ s, f a) :=
  Finset.sum_induction f NonnegCoeffs (fun _ _ => NonnegCoeffs.add) NonnegCoeffs.zero h

/-- Non-negative coefficients are closed under finite products. -/
theorem NonnegCoeffs.prod {α : Type*} {s : Finset α} {f : α → MvPolynomial (ι ⊕ ι) ℝ}
    (h : ∀ a ∈ s, NonnegCoeffs (f a)) : NonnegCoeffs (∏ a ∈ s, f a) :=
  Finset.prod_induction f NonnegCoeffs (fun _ _ => NonnegCoeffs.mul) NonnegCoeffs.one h

/-- Non-negative coefficients are closed under powers. -/
theorem NonnegCoeffs.pow {p : MvPolynomial (ι ⊕ ι) ℝ} (hp : NonnegCoeffs p) :
    ∀ k : ℕ, NonnegCoeffs (p ^ k)
  | 0 => by simpa using NonnegCoeffs.one
  | k + 1 => by rw [pow_succ]; exact (NonnegCoeffs.pow hp k).mul hp

/-! ## The integral of a non-negative-coefficient polynomial is non-negative -/

/-- Integrability of a single site-product `∏ᵢ tᵢ^{aᵢ} qᵢ^{bᵢ}·siteWeightᵢ`. -/
theorem integrable_monomial_mul_siteWeightProd [Fintype ι] {A σ c₁ c₂ : ℝ} (hA : 0 < A)
    (a b : ι → ℕ) :
    Integrable (fun ξ : VectorConfig ι =>
      ∏ i, ((ξ i).1 ^ a i * (ξ i).2 ^ b i * siteWeight A σ c₁ c₂ (ξ i))) := by
  rw [volume_pi]
  exact Integrable.fintype_prod fun i => integrable_pow_mul_siteWeight hA (a i) (b i)

/-- The integral of a single site-product factorises into single-site moments. -/
theorem integral_monomial_mul_siteWeightProd [Fintype ι] {A σ c₁ c₂ : ℝ} (a b : ι → ℕ) :
    ∫ ξ : VectorConfig ι, ∏ i, ((ξ i).1 ^ a i * (ξ i).2 ^ b i * siteWeight A σ c₁ c₂ (ξ i))
      = ∏ i, ∫ ξ : ℝ × ℝ, ξ.1 ^ a i * ξ.2 ^ b i * siteWeight A σ c₁ c₂ ξ :=
  integral_fintype_prod_volume_eq_prod
    (fun i ξ => ξ.1 ^ a i * ξ.2 ^ b i * siteWeight A σ c₁ c₂ ξ)

/-- **The integral of a non-negative-coefficient spin polynomial against the
product weight is non-negative.**  Expanding `eval` into monomials
(`eval_eq'`), each monomial integral factorises (`Fintype.prod_sum_type`,
`integral_fintype_prod_volume_eq_prod`) into single-site field moments, each
`≥ 0` by `singleSpinMoment_field_nonneg`; the non-negative coefficients keep the
total `≥ 0`. -/
theorem spinEval_integral_nonneg [Fintype ι] {A σ c₁ c₂ : ℝ} (hA : 0 < A) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂)
    {p : MvPolynomial (ι ⊕ ι) ℝ} (hp : NonnegCoeffs p) :
    0 ≤ ∫ ξ : VectorConfig ι, spinEval p ξ * ∏ i, siteWeight A σ c₁ c₂ (ξ i) := by
  classical
  have hpt : ∀ ξ : VectorConfig ι, spinEval p ξ * ∏ i, siteWeight A σ c₁ c₂ (ξ i)
      = ∑ d ∈ p.support, p.coeff d *
          ∏ i, ((ξ i).1 ^ d (Sum.inl i) * (ξ i).2 ^ d (Sum.inr i)
            * siteWeight A σ c₁ c₂ (ξ i)) := by
    intro ξ
    rw [spinEval, eval_eq', Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [mul_assoc]
    congr 1
    have hsplit : (∏ v, spinVal ξ v ^ d v)
        = (∏ i, (ξ i).1 ^ d (Sum.inl i)) * ∏ i, (ξ i).2 ^ d (Sum.inr i) := by
      rw [Fintype.prod_sum_type (f := fun v => spinVal ξ v ^ d v)]
      simp only [spinVal, Sum.elim_inl, Sum.elim_inr]
    rw [hsplit, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  simp_rw [hpt]
  have hintegr : ∀ d : (ι ⊕ ι) →₀ ℕ, Integrable (fun ξ : VectorConfig ι =>
      p.coeff d * ∏ i, ((ξ i).1 ^ d (Sum.inl i) * (ξ i).2 ^ d (Sum.inr i)
        * siteWeight A σ c₁ c₂ (ξ i))) :=
    fun d => (integrable_monomial_mul_siteWeightProd hA
      (fun i => d (Sum.inl i)) (fun i => d (Sum.inr i))).const_mul _
  rw [integral_finset_sum _ (fun d _ => hintegr d)]
  refine Finset.sum_nonneg fun d _ => ?_
  rw [integral_const_mul, integral_monomial_mul_siteWeightProd]
  exact mul_nonneg (hp d) (Finset.prod_nonneg fun i _ => siteMoment_nonneg hA hc₁ hc₂ _ _)

/-! ## The truncating polynomials -/

/-- The per-edge inner-product polynomial `X(inl i)·X(inl j) + X(inr i)·X(inr j)`. -/
noncomputable def edgeDotPoly (e : Sym2 ι) : MvPolynomial (ι ⊕ ι) ℝ :=
  Sym2.lift ⟨fun i j => X (Sum.inl i) * X (Sum.inl j) + X (Sum.inr i) * X (Sum.inr j),
    fun i j => by ring⟩ e

/-- The interaction-sum polynomial `S = ∑_e edgeDotPoly e`. -/
noncomputable def interactionPoly (G : SimpleGraph ι) [Fintype G.edgeSet] :
    MvPolynomial (ι ⊕ ι) ℝ :=
  ∑ e ∈ G.edgeFinset, edgeDotPoly e

/-- The monomial polynomial `∏_{i∈A} X(inl i) · ∏_{j∈B} X(inr j)`. -/
noncomputable def monoPoly (Av Bv : Finset ι) : MvPolynomial (ι ⊕ ι) ℝ :=
  (∏ i ∈ Av, X (Sum.inl i)) * ∏ j ∈ Bv, X (Sum.inr j)

/-- The truncated integrand polynomial
`monoPoly Av Bv · ∑_{k<N} C((βJ)ᵏ/k!)·interactionPolyᵏ`, whose `spinEval` is
`vectorMonomial Av Bv · expTrunc N (βJ·S)`. -/
noncomputable def truncPoly (G : SimpleGraph ι) [Fintype G.edgeSet] (Av Bv : Finset ι)
    (J β : ℝ) (N : ℕ) : MvPolynomial (ι ⊕ ι) ℝ :=
  monoPoly Av Bv *
    ∑ k ∈ Finset.range N, C ((β * J) ^ k / k.factorial) * interactionPoly G ^ k

/-- `spinEval` of a variable recovers the corresponding spin component. -/
@[simp] theorem spinEval_X_inl (i : ι) (ξ : VectorConfig ι) :
    spinEval (X (Sum.inl i) : MvPolynomial (ι ⊕ ι) ℝ) ξ = (ξ i).1 := by
  simp [spinEval, spinVal]

@[simp] theorem spinEval_X_inr (i : ι) (ξ : VectorConfig ι) :
    spinEval (X (Sum.inr i) : MvPolynomial (ι ⊕ ι) ℝ) ξ = (ξ i).2 := by
  simp [spinEval, spinVal]

/-- `spinEval (edgeDotPoly e)` is the per-edge inner product `vEdgeDot`. -/
theorem spinEval_edgeDotPoly (e : Sym2 ι) (ξ : VectorConfig ι) :
    spinEval (edgeDotPoly e) ξ = vEdgeDot ξ e := by
  induction e using Sym2.ind with
  | _ i j =>
    simp only [edgeDotPoly, Sym2.lift_mk, spinEval, map_add, map_mul, eval_X,
      vEdgeDot, vDot, vSpinT, vSpinQ, spinVal, Sum.elim_inl, Sum.elim_inr]

/-- `spinEval (interactionPoly G)` is the interaction sum `∑_e ξᵢ·ξⱼ`. -/
theorem spinEval_interactionPoly (G : SimpleGraph ι) [Fintype G.edgeSet] (ξ : VectorConfig ι) :
    spinEval (interactionPoly G) ξ = ∑ e ∈ G.edgeFinset, vEdgeDot ξ e := by
  rw [interactionPoly, spinEval, map_sum]
  exact Finset.sum_congr rfl fun e _ => spinEval_edgeDotPoly e ξ

/-- `spinEval (monoPoly Av Bv)` is the spin monomial `vectorMonomial`. -/
theorem spinEval_monoPoly (Av Bv : Finset ι) (ξ : VectorConfig ι) :
    spinEval (monoPoly Av Bv) ξ = vectorMonomial Av Bv ξ := by
  rw [monoPoly, spinEval, map_mul, map_prod, map_prod, vectorMonomial]
  congr 1 <;>
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [eval_X, spinVal, Sum.elim_inl, Sum.elim_inr, vSpinT, vSpinQ]

/-- **`spinEval (truncPoly …)` is the truncated integrand**
`vectorMonomial Av Bv · expTrunc N (βJ·S)`. -/
theorem spinEval_truncPoly (G : SimpleGraph ι) [Fintype G.edgeSet] (Av Bv : Finset ι)
    (J β : ℝ) (N : ℕ) (ξ : VectorConfig ι) :
    spinEval (truncPoly G Av Bv J β N) ξ
      = vectorMonomial Av Bv ξ
        * expTrunc N (β * J * ∑ e ∈ G.edgeFinset, vEdgeDot ξ e) := by
  rw [truncPoly, spinEval, map_mul,
    show eval (spinVal ξ) (monoPoly Av Bv) = vectorMonomial Av Bv ξ from
      spinEval_monoPoly Av Bv ξ]
  congr 1
  rw [map_sum, expTrunc]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, eval_C,
    show eval (spinVal ξ) (interactionPoly G) = ∑ e ∈ G.edgeFinset, vEdgeDot ξ e from
      spinEval_interactionPoly G ξ, mul_pow]
  ring

/-- The truncating polynomial has non-negative coefficients (ferromagnetic
`β, J ≥ 0`). -/
theorem truncPoly_nonnegCoeffs (G : SimpleGraph ι) [Fintype G.edgeSet] (Av Bv : Finset ι)
    {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (N : ℕ) :
    NonnegCoeffs (truncPoly G Av Bv J β N) := by
  have hedge : NonnegCoeffs (interactionPoly G) :=
    NonnegCoeffs.sum fun e _ => by
      induction e using Sym2.ind with
      | _ i j =>
        rw [edgeDotPoly, Sym2.lift_mk]
        exact ((NonnegCoeffs.X _).mul (NonnegCoeffs.X _)).add
          ((NonnegCoeffs.X _).mul (NonnegCoeffs.X _))
  rw [truncPoly]
  refine NonnegCoeffs.mul ?_ (NonnegCoeffs.sum fun k _ => ?_)
  · rw [monoPoly]
    exact (NonnegCoeffs.prod fun i _ => NonnegCoeffs.X _).mul
      (NonnegCoeffs.prod fun j _ => NonnegCoeffs.X _)
  · exact (NonnegCoeffs.C (div_nonneg (pow_nonneg (mul_nonneg hβ hJ) k)
      (by positivity))).mul (hedge.pow k)

/-! ## The Gibbs weight as a product weight -/

/-- The product of single-site weights equals the exponential of the field minus
potential. -/
theorem prod_siteWeight_eq [Fintype ι] (A σ c₁ c₂ : ℝ) (ξ : VectorConfig ι) :
    ∏ i, siteWeight A σ c₁ c₂ (ξ i)
      = Real.exp ((∑ i, (c₁ * (ξ i).1 + c₂ * (ξ i).2)) - vectorPotentialSum A σ ξ) := by
  have hpt : ∀ i, siteWeight A σ c₁ c₂ (ξ i)
      = Real.exp ((c₁ * (ξ i).1 + c₂ * (ξ i).2)
          - twoCompPotential A σ (vSpinT ξ i) (vSpinQ ξ i)) := by
    intro i
    rw [siteWeight, singleSpinDensity, ← Real.exp_add, twoCompPotential]
    congr 1
    simp only [vSpinT, vSpinQ]; ring
  rw [Finset.prod_congr rfl fun i _ => hpt i, ← Real.exp_sum, vectorPotentialSum,
    Finset.sum_sub_distrib]

/-- **The two-component Gibbs weight factorises** as
`exp(βJ·S) · ∏ᵢ siteWeight A σ (βh¹) (βh²)`. -/
theorem vectorWeight_eq_exp_mul_siteWeightProd [Fintype ι] (G : SimpleGraph ι)
    [Fintype G.edgeSet] (A σ J h1 h2 β : ℝ) (ξ : VectorConfig ι) :
    vectorWeight G A σ J h1 h2 β ξ
      = Real.exp (β * J * ∑ e ∈ G.edgeFinset, vEdgeDot ξ e)
        * ∏ i, siteWeight A σ (β * h1) (β * h2) (ξ i) := by
  rw [prod_siteWeight_eq, vectorWeight, vectorHamiltonian, ← Real.exp_add]
  congr 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [vSpinT, vSpinQ]
  ring

/-! ## The uniform dominating bound -/

/-- An indicator product collapses to a product over the indicating set. -/
theorem prod_abs_pow_indicator [Fintype ι] [DecidableEq ι] (s : Finset ι) (g : ι → ℝ) :
    (∏ i, |g i| ^ (if i ∈ s then 1 else 0)) = ∏ i ∈ s, |g i| := by
  rw [show (∏ i, |g i| ^ (if i ∈ s then 1 else 0)) = ∏ i, (if i ∈ s then |g i| else 1) from
    Finset.prod_congr rfl fun i _ => by split <;> simp]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- **The truncated integrand is dominated, uniformly in `N`, by an integrable
product weight.**  The truncated exponential is bounded by `exp(cc·∑|ξᵢ|²)` (AM-GM
on the inner products), which raises the per-site quadratic coefficient from `σ`
to `σ − cc`; the monomial factor splits per site via `prod_abs_pow_indicator`. -/
theorem norm_truncIntegrand_le_dom [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [Fintype G.edgeSet]
    {A σ J β c₁ c₂ : ℝ} (Av Bv : Finset ι) (N : ℕ) (ξ : VectorConfig ι) :
    ‖vectorMonomial Av Bv ξ * expTrunc N (β * J * ∑ e ∈ G.edgeFinset, vEdgeDot ξ e)
        * ∏ i, siteWeight A σ c₁ c₂ (ξ i)‖
      ≤ ∏ i, (|(ξ i).1| ^ (if i ∈ Av then 1 else 0) * |(ξ i).2| ^ (if i ∈ Bv then 1 else 0)
          * siteWeight A (σ - |β * J| * (G.edgeFinset.card : ℝ)) c₁ c₂ (ξ i)) := by
  set S : ℝ := ∑ e ∈ G.edgeFinset, vEdgeDot ξ e with hS
  set cc : ℝ := |β * J| * (G.edgeFinset.card : ℝ) with hcc
  set W : ℝ := ∏ i, siteWeight A σ c₁ c₂ (ξ i) with hW
  have hWpos : 0 < W := Finset.prod_pos fun i _ => siteWeight_pos _ _ _ _ _
  have hLHS : ‖vectorMonomial Av Bv ξ * expTrunc N (β * J * S) * W‖
      = |vectorMonomial Av Bv ξ| * |expTrunc N (β * J * S)| * W := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hWpos]
  have hEN : |expTrunc N (β * J * S)| ≤ Real.exp (cc * ∑ i, normSq ξ i) := by
    calc |expTrunc N (β * J * S)| ≤ Real.exp |β * J * S| := abs_expTrunc_le_exp_abs _ _
      _ ≤ Real.exp (cc * ∑ i, normSq ξ i) := by
          refine Real.exp_le_exp.mpr ?_
          calc |β * J * S| = |β * J| * |S| := by rw [abs_mul]
            _ ≤ |β * J| * ∑ e ∈ G.edgeFinset, |vEdgeDot ξ e| :=
                mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
            _ ≤ |β * J| * ∑ _e ∈ G.edgeFinset, ∑ i, normSq ξ i :=
                mul_le_mul_of_nonneg_left
                  (Finset.sum_le_sum fun e _ => abs_vEdgeDot_le_sum_normSq ξ e) (abs_nonneg _)
            _ = cc * ∑ i, normSq ξ i := by
                rw [Finset.sum_const, nsmul_eq_mul, hcc]; ring
  have hsw : ∏ i, siteWeight A (σ - cc) c₁ c₂ (ξ i) = Real.exp (cc * ∑ i, normSq ξ i) * W := by
    have hpt : ∀ i, siteWeight A (σ - cc) c₁ c₂ (ξ i)
        = Real.exp (cc * normSq ξ i) * siteWeight A σ c₁ c₂ (ξ i) := by
      intro i
      simp only [siteWeight, singleSpinDensity, normSq, vSpinT, vSpinQ, ← Real.exp_add]
      congr 1; ring
    rw [Finset.prod_congr rfl fun i _ => hpt i, Finset.prod_mul_distrib, ← Real.exp_sum,
      ← Finset.mul_sum, hW]
  have habs_M : |vectorMonomial Av Bv ξ|
      = (∏ i, |(ξ i).1| ^ (if i ∈ Av then 1 else 0))
        * ∏ i, |(ξ i).2| ^ (if i ∈ Bv then 1 else 0) := by
    rw [vectorMonomial, abs_mul, Finset.abs_prod, Finset.abs_prod]
    simp only [vSpinT, vSpinQ]
    rw [← prod_abs_pow_indicator Av (fun i => (ξ i).1),
      ← prod_abs_pow_indicator Bv (fun i => (ξ i).2)]
  have hRHS : (∏ i, (|(ξ i).1| ^ (if i ∈ Av then 1 else 0)
        * |(ξ i).2| ^ (if i ∈ Bv then 1 else 0) * siteWeight A (σ - cc) c₁ c₂ (ξ i)))
      = |vectorMonomial Av Bv ξ| * (Real.exp (cc * ∑ i, normSq ξ i) * W) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hsw, ← habs_M]
  rw [hLHS, hRHS]
  calc |vectorMonomial Av Bv ξ| * |expTrunc N (β * J * S)| * W
      = |vectorMonomial Av Bv ξ| * (|expTrunc N (β * J * S)| * W) := by ring
    _ ≤ |vectorMonomial Av Bv ξ| * (Real.exp (cc * ∑ i, normSq ξ i) * W) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hEN hWpos.le) (abs_nonneg _)

/-! ## The first inequality -/

/-- **First Griffiths inequality for two-component spins** (GJ Theorem 4.7.1,
first inequality, p. 70): for `A > 0`, ferromagnetic `β, J ≥ 0` and a
non-negative external field `h¹, h² ≥ 0`, every monomial correlation is
non-negative, `0 ≤ ⟨∏_{i∈A} tᵢ · ∏_{j∈B} qⱼ⟩`.

The proof truncates the interaction exponential to a non-negative-coefficient
polynomial, whose integral is non-negative by `spinEval_integral_nonneg`, and
passes to the limit by dominated convergence. -/
theorem vectorCorrelation_nonneg [Fintype ι] (G : SimpleGraph ι) [Fintype G.edgeSet]
    {A : ℝ} {σ J h1 h2 β : ℝ} (hA : 0 < A) (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (hh1 : 0 ≤ h1) (hh2 : 0 ≤ h2) (Av Bv : Finset ι) :
    0 ≤ vectorCorrelation G A σ J h1 h2 β Av Bv := by
  classical
  rw [vectorCorrelation, vectorExpectation]
  refine mul_nonneg (inv_nonneg.mpr (vectorPartition_pos G σ J h1 h2 β hA).le) ?_
  -- Reduce the numerator to the product-weight form.
  set c₁ : ℝ := β * h1 with hc₁def
  set c₂ : ℝ := β * h2 with hc₂def
  have hc₁ : 0 ≤ c₁ := mul_nonneg hβ hh1
  have hc₂ : 0 ≤ c₂ := mul_nonneg hβ hh2
  have hwe : ∀ ξ : VectorConfig ι,
      vectorMonomial Av Bv ξ * vectorWeight G A σ J h1 h2 β ξ
        = vectorMonomial Av Bv ξ * Real.exp (β * J * ∑ e ∈ G.edgeFinset, vEdgeDot ξ e)
            * ∏ i, siteWeight A σ c₁ c₂ (ξ i) := by
    intro ξ; rw [vectorWeight_eq_exp_mul_siteWeightProd]; ring
  simp_rw [hwe]
  -- The truncated integrand and its non-negativity.
  set fN : ℕ → VectorConfig ι → ℝ := fun N ξ =>
    vectorMonomial Av Bv ξ * expTrunc N (β * J * ∑ e ∈ G.edgeFinset, vEdgeDot ξ e)
      * ∏ i, siteWeight A σ c₁ c₂ (ξ i) with hfN
  have hge : ∀ N, 0 ≤ ∫ ξ, fN N ξ := by
    intro N
    have heq : ∀ ξ : VectorConfig ι,
        fN N ξ = spinEval (truncPoly G Av Bv J β N) ξ * ∏ i, siteWeight A σ c₁ c₂ (ξ i) := by
      intro ξ; rw [hfN, spinEval_truncPoly]
    simp_rw [heq]
    exact spinEval_integral_nonneg hA hc₁ hc₂ (truncPoly_nonnegCoeffs G Av Bv hβ hJ N)
  -- The uniform AM-GM dominator.
  set Gdom : VectorConfig ι → ℝ := fun ξ =>
    ∏ i, (|(ξ i).1| ^ (if i ∈ Av then 1 else 0) * |(ξ i).2| ^ (if i ∈ Bv then 1 else 0)
      * siteWeight A (σ - |β * J| * (G.edgeFinset.card : ℝ)) c₁ c₂ (ξ i)) with hGdom
  have hGdom_int : Integrable Gdom := by
    rw [hGdom, volume_pi]
    exact Integrable.fintype_prod fun i =>
      integrable_abs_pow_mul_siteWeight hA (if i ∈ Av then 1 else 0) (if i ∈ Bv then 1 else 0)
  -- Dominated convergence.
  have hlim : Filter.Tendsto (fun N => ∫ ξ, fN N ξ) Filter.atTop
      (nhds (∫ ξ : VectorConfig ι,
        vectorMonomial Av Bv ξ * Real.exp (β * J * ∑ e ∈ G.edgeFinset, vEdgeDot ξ e)
          * ∏ i, siteWeight A σ c₁ c₂ (ξ i))) := by
    refine tendsto_integral_of_dominated_convergence Gdom (fun N => ?_) hGdom_int
      (fun N => ?_) ?_
    · -- measurability of fN N
      have hc : Continuous (fN N) := by
        simp only [hfN]
        refine ((continuous_vectorMonomial Av Bv).mul ?_).mul ?_
        · exact (continuous_expTrunc N).comp (continuous_const.mul
            (continuous_finset_sum _ fun e _ => continuous_vEdgeDot e))
        · exact continuous_finset_prod _ fun i _ =>
            (continuous_siteWeight A σ c₁ c₂).comp (continuous_apply i)
      exact hc.aestronglyMeasurable
    · -- pointwise bound ‖fN N ξ‖ ≤ Gdom ξ
      refine Filter.Eventually.of_forall fun ξ => ?_
      simp only [hfN, hGdom]
      exact norm_truncIntegrand_le_dom G Av Bv N ξ
    · -- pointwise convergence
      refine Filter.Eventually.of_forall fun ξ => ?_
      simp only [hfN]
      exact (tendsto_const_nhds.mul (tendsto_expTrunc _)).mul tendsto_const_nhds
  exact ge_of_tendsto' hlim hge

end IsingModel.ContinuousSpin
