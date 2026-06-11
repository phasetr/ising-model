import IsingModel.Inequalities.Lebowitz.FourfoldSystem

/-!
# Joint u-moments of the fourfold system (GJ §4.3)

The configuration-sum machinery behind GJ Theorem 4.3.1: joint monomials in the site-indexed
Hadamard variables with arbitrary ℕ exponents, their site factorisation into single-site
moments (hence non-negativity, by `siteMoment_nonneg`), and the `HasNonnegUMoments`
invariant — closed under multiplication by u-monomials — that the ferromagnetic expansion of
the fourfold Boltzmann weight will preserve.

* `quadConfigEquiv` — fourfold configurations as site-indexed quadruples.
* `uMonomial` — joint u-monomials with site-indexed exponents.
* `sum_uMonomial_eq_prod` / `sum_uMonomial_nonneg` — site factorisation and positivity.
* `HasNonnegUMoments` — the expansion invariant, with the constant and monomial-shift
  closure properties.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.3,
Theorem 4.3.1, pp. 59–61.
-/

namespace IsingModel

namespace Lebowitz

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The fourfold configuration space as site-indexed single-site quadruples. -/
def quadConfigEquiv (ι : Type*) : QuadConfig ι ≃ (ι → SiteQuad) where
  toFun v i := siteQuadAt v i
  invFun w :=
    (fun i => (w i).1, fun i => (w i).2.1, fun i => (w i).2.2.1, fun i => (w i).2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Joint u-monomial** with site-indexed exponents:
`∏ᵢ u₁(i)^{k i} · u₂(i)^{l i} · u₃(i)^{m i} · u₄(i)^{n i}`. -/
noncomputable def uMonomial (k l m n : ι → ℕ) (v : QuadConfig ι) : ℝ :=
  ∏ i, (uSite₁ i v ^ k i * uSite₂ i v ^ l i * uSite₃ i v ^ m i * uSite₄ i v ^ n i)

omit [DecidableEq ι] in
/-- u-monomials multiply by adding exponents. -/
theorem uMonomial_mul (k l m n k' l' m' n' : ι → ℕ) (v : QuadConfig ι) :
    uMonomial k l m n v * uMonomial k' l' m' n' v
      = uMonomial (k + k') (l + l') (m + m') (n + n') v := by
  unfold uMonomial
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, pow_add]
  ring

/-- **Site factorisation**: the configuration sum of a joint u-monomial is the product of the
single-site moments. -/
theorem sum_uMonomial_eq_prod (k l m n : ι → ℕ) :
    ∑ v : QuadConfig ι, uMonomial k l m n v
      = ∏ i, siteMoment (k i) (l i) (m i) (n i) := by
  rw [← Equiv.sum_comp (quadConfigEquiv ι).symm (fun v => uMonomial k l m n v)]
  have hsummand : ∀ w : ι → SiteQuad,
      uMonomial k l m n ((quadConfigEquiv ι).symm w)
        = ∏ i, (u₁ (w i) ^ k i * u₂ (w i) ^ l i * u₃ (w i) ^ m i * u₄ (w i) ^ n i) := by
    intro w
    unfold uMonomial uSite₁ uSite₂ uSite₃ uSite₄
    refine Finset.prod_congr rfl fun i _ => ?_
    rfl
  simp_rw [hsummand]
  unfold siteMoment
  rw [← Fintype.piFinset_univ]
  exact (Finset.prod_univ_sum (fun _ => (Finset.univ : Finset SiteQuad))
    (fun i q => u₁ q ^ k i * u₂ q ^ l i * u₃ q ^ m i * u₄ q ^ n i)).symm

/-- **Positivity of u-monomial configuration sums** (the system-level Ising (4.3.6)). -/
theorem sum_uMonomial_nonneg (k l m n : ι → ℕ) :
    0 ≤ ∑ v : QuadConfig ι, uMonomial k l m n v := by
  rw [sum_uMonomial_eq_prod]
  exact Finset.prod_nonneg fun i _ => siteMoment_nonneg (k i) (l i) (m i) (n i)

/-- A function on fourfold configurations has **non-negative u-moments** if its configuration
sum against every joint u-monomial is non-negative — the invariant preserved by the
ferromagnetic expansion of the fourfold weight. -/
def HasNonnegUMoments (f : QuadConfig ι → ℝ) : Prop :=
  ∀ k l m n : ι → ℕ, 0 ≤ ∑ v : QuadConfig ι, uMonomial k l m n v * f v

/-- The constant function `1` has non-negative u-moments. -/
theorem hasNonnegUMoments_one : HasNonnegUMoments (ι := ι) fun _ => 1 := by
  intro k l m n
  simpa using sum_uMonomial_nonneg k l m n

/-- Multiplication by a joint u-monomial preserves non-negative u-moments. -/
theorem HasNonnegUMoments.mul_uMonomial {f : QuadConfig ι → ℝ}
    (hf : HasNonnegUMoments f) (k' l' m' n' : ι → ℕ) :
    HasNonnegUMoments fun v => uMonomial k' l' m' n' v * f v := by
  intro k l m n
  have hsummand : ∀ v : QuadConfig ι,
      uMonomial k l m n v * (uMonomial k' l' m' n' v * f v)
        = uMonomial (k + k') (l + l') (m + m') (n + n') v * f v := by
    intro v
    rw [← mul_assoc, uMonomial_mul]
  simp_rw [hsummand]
  exact hf (k + k') (l + l') (m + m') (n + n')

end Lebowitz

end IsingModel
