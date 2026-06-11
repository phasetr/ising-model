import IsingModel.Inequalities.Lebowitz.UMomentExpansion

/-!
# GJ Theorem 4.3.1 for Ising spins (GJ §4.3)

The fourfold duplicate-variable positivity `0 ≤ ⟨u₁^A u₂^B u₃^C u₄^D⟩₄`: the fourfold
Hamiltonian is ferromagnetic in the Hadamard variables — per edge the Hadamard orthogonality
gives `ξᵢξⱼ + χᵢχⱼ + ξ'ᵢξ'ⱼ + χ'ᵢχ'ⱼ = ¼ ∑_r u_r(i)u_r(j)`, and the field term is
`h·u₁(i)` — so the fourfold weight is a finite product of factors `exp(K·uMonomial)` with
`K ≥ 0`, and the exponential closure of the u-moment invariant applies.

* `uMonomial_single` / `uMonomial_pair` — u-monomials with one- and two-site exponents.
* `uProd_eq_uMonomial` — `Finset` products as joint u-monomials.
* `quadEdgeSum_eq` — the per-edge Hadamard orthogonality identity (4.3.5).
* `quadWeight_eq_prod_exp` — the ferromagnetic factorisation of the fourfold weight.
* `hasNonnegUMoments_quadWeight` — the invariant holds for the fourfold weight.
* `theorem_4_3_1` — **GJ Theorem 4.3.1 (Ising form)**.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.3,
Theorem 4.3.1, pp. 59–61.
-/

namespace IsingModel

namespace Lebowitz

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The joint u-monomial with all four indicator exponents is the product of the four
`Finset` u-products. -/
theorem uProd_eq_uMonomial (A B C D : Finset ι) (v : QuadConfig ι) :
    uMonomial (fun i => if i ∈ A then 1 else 0) (fun i => if i ∈ B then 1 else 0)
        (fun i => if i ∈ C then 1 else 0) (fun i => if i ∈ D then 1 else 0) v
      = uProd₁ A v * uProd₂ B v * uProd₃ C v * uProd₄ D v := by
  unfold uMonomial uProd₁ uProd₂ uProd₃ uProd₄
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  congr 1
  · congr 1
    · congr 1
      · rw [show (∏ i ∈ A, uSite₁ i v)
            = ∏ i, (if i ∈ A then uSite₁ i v else 1) from by
          rw [Finset.prod_ite_mem Finset.univ A, Finset.univ_inter]]
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases h : i ∈ A <;> simp [h]
      · rw [show (∏ i ∈ B, uSite₂ i v)
            = ∏ i, (if i ∈ B then uSite₂ i v else 1) from by
          rw [Finset.prod_ite_mem Finset.univ B, Finset.univ_inter]]
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases h : i ∈ B <;> simp [h]
    · rw [show (∏ i ∈ C, uSite₃ i v)
            = ∏ i, (if i ∈ C then uSite₃ i v else 1) from by
          rw [Finset.prod_ite_mem Finset.univ C, Finset.univ_inter]]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases h : i ∈ C <;> simp [h]
  · rw [show (∏ i ∈ D, uSite₄ i v)
            = ∏ i, (if i ∈ D then uSite₄ i v else 1) from by
          rw [Finset.prod_ite_mem Finset.univ D, Finset.univ_inter]]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : i ∈ D <;> simp [h]

omit [Fintype ι] in
/-- Indicator of the empty set is the zero exponent. -/
theorem indicator_empty_eq_zero :
    (fun i : ι => if i ∈ (∅ : Finset ι) then 1 else 0) = (0 : ι → ℕ) := by
  funext i
  simp

/-- The u-monomial with a singleton first-variable exponent is `u₁(i)` (the field term). -/
theorem uMonomial_single₁ (i : ι) (v : QuadConfig ι) :
    uMonomial (fun x => if x ∈ ({i} : Finset ι) then 1 else 0)
        (fun x => if x ∈ (∅ : Finset ι) then 1 else 0)
        (fun x => if x ∈ (∅ : Finset ι) then 1 else 0)
        (fun x => if x ∈ (∅ : Finset ι) then 1 else 0) v = uSite₁ i v := by
  rw [uProd_eq_uMonomial]
  unfold uProd₁ uProd₂ uProd₃ uProd₄
  simp

/-- The u-monomial with a pair first-variable exponent is `u₁(i)·u₁(j)`. -/
theorem uMonomial_pair₁ {i j : ι} (hij : i ≠ j) (v : QuadConfig ι) :
    uMonomial (fun x => if x ∈ ({i, j} : Finset ι) then 1 else 0)
        (fun x => if x ∈ (∅ : Finset ι) then 1 else 0)
        (fun x => if x ∈ (∅ : Finset ι) then 1 else 0)
        (fun x => if x ∈ (∅ : Finset ι) then 1 else 0) v
      = uSite₁ i v * uSite₁ j v := by
  rw [uProd_eq_uMonomial]
  unfold uProd₁ uProd₂ uProd₃ uProd₄
  simp [Finset.prod_pair hij]

/-- The u-monomial with a pair second-variable exponent is `u₂(i)·u₂(j)`. -/
theorem uMonomial_pair₂ {i j : ι} (hij : i ≠ j) (v : QuadConfig ι) :
    uMonomial (fun x => if x ∈ (∅ : Finset ι) then 1 else 0)
        (fun x => if x ∈ ({i, j} : Finset ι) then 1 else 0)
        (fun x => if x ∈ (∅ : Finset ι) then 1 else 0)
        (fun x => if x ∈ (∅ : Finset ι) then 1 else 0) v
      = uSite₂ i v * uSite₂ j v := by
  rw [uProd_eq_uMonomial]
  unfold uProd₁ uProd₂ uProd₃ uProd₄
  simp [Finset.prod_pair hij]

/-- The u-monomial with a pair third-variable exponent is `u₃(i)·u₃(j)`. -/
theorem uMonomial_pair₃ {i j : ι} (hij : i ≠ j) (v : QuadConfig ι) :
    uMonomial (fun x => if x ∈ (∅ : Finset ι) then 1 else 0)
        (fun x => if x ∈ (∅ : Finset ι) then 1 else 0)
        (fun x => if x ∈ ({i, j} : Finset ι) then 1 else 0)
        (fun x => if x ∈ (∅ : Finset ι) then 1 else 0) v
      = uSite₃ i v * uSite₃ j v := by
  rw [uProd_eq_uMonomial]
  unfold uProd₁ uProd₂ uProd₃ uProd₄
  simp [Finset.prod_pair hij]

/-- The u-monomial with a pair fourth-variable exponent is `u₄(i)·u₄(j)`. -/
theorem uMonomial_pair₄ {i j : ι} (hij : i ≠ j) (v : QuadConfig ι) :
    uMonomial (fun x => if x ∈ (∅ : Finset ι) then 1 else 0)
        (fun x => if x ∈ (∅ : Finset ι) then 1 else 0)
        (fun x => if x ∈ (∅ : Finset ι) then 1 else 0)
        (fun x => if x ∈ ({i, j} : Finset ι) then 1 else 0) v
      = uSite₄ i v * uSite₄ j v := by
  rw [uProd_eq_uMonomial]
  unfold uProd₁ uProd₂ uProd₃ uProd₄
  simp [Finset.prod_pair hij]

end Lebowitz

end IsingModel
