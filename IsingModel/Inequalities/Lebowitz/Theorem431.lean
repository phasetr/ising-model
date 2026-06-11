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
* `uEdge` / `quadWeight_eq_exp` — the per-edge Hadamard quantities and the ferromagnetic
  exponent identity (4.3.5).
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

/-- The per-edge Hadamard product of the `r`-th variables, as a function on `Sym2 ι`
(symmetric, hence a well-defined edge quantity, like `edgeSpin`). -/
noncomputable def uEdge (r : Fin 4) (e : Sym2 ι) (v : QuadConfig ι) : ℝ :=
  Sym2.lift ⟨fun i j =>
      (match r with
        | 0 => uSite₁ i v * uSite₁ j v
        | 1 => uSite₂ i v * uSite₂ j v
        | 2 => uSite₃ i v * uSite₃ j v
        | 3 => uSite₄ i v * uSite₄ j v),
    fun i j => by fin_cases r <;> simp [mul_comm]⟩ e

/-- **Exponential-of-sum closure (existential witnesses)**: multiplying an HNU function by
`exp(∑ₜ gₜ)` preserves non-negative u-moments when every `gₜ` is a non-negative multiple of a
joint u-monomial. -/
theorem hasNonnegUMoments_exp_sum_mul {T : Type*} (s : Finset T)
    (g : T → QuadConfig ι → ℝ)
    (hg : ∀ t ∈ s, ∃ (K : ℝ) (k₀ l₀ m₀ n₀ : ι → ℕ), 0 ≤ K ∧
      ∀ v, g t v = K * uMonomial k₀ l₀ m₀ n₀ v)
    {f : QuadConfig ι → ℝ} (hf : HasNonnegUMoments f) :
    HasNonnegUMoments fun v => Real.exp (∑ t ∈ s, g t v) * f v := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hf
  | @insert x s' hx ih =>
    obtain ⟨K, k₀, l₀, m₀, n₀, hK, hgx⟩ := hg x (Finset.mem_insert_self x s')
    have hrw : (fun v => Real.exp (∑ t ∈ insert x s', g t v) * f v)
        = fun v => Real.exp (K * uMonomial k₀ l₀ m₀ n₀ v) *
            (Real.exp (∑ t ∈ s', g t v) * f v) := by
      funext v
      rw [Finset.sum_insert hx, Real.exp_add, hgx v]
      ring
    rw [hrw]
    exact (ih fun t ht => hg t (Finset.mem_insert_of_mem ht)).mul_exp hK k₀ l₀ m₀ n₀

omit [DecidableEq ι] in
/-- **The ferromagnetic exponent identity (4.3.5)**: the fourfold Boltzmann weight is the
exponential of a ferromagnetic sum of joint u-monomials — per edge the Hadamard
orthogonality gives `∑_{copies} edgeSpin = ¼ ∑_r uEdge_r`, and the field term is
`h·u₁(i)`. -/
theorem quadWeight_eq_exp (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (v : QuadConfig ι) :
    quadWeight G p v
      = Real.exp (∑ er ∈ G.edgeFinset ×ˢ (Finset.univ : Finset (Fin 4)),
          p.β * p.J / 4 * uEdge er.2 er.1 v) *
        Real.exp (∑ i, p.β * p.h * uSite₁ i v) := by
  unfold quadWeight boltzmannWeight
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold hamiltonian interactionEnergy externalFieldEnergy
  rw [Finset.sum_product]
  have hedge : ∀ e ∈ G.edgeFinset,
      ∑ r : Fin 4, p.β * p.J / 4 * uEdge r e v
        = p.β * p.J * (edgeSpin (K := ℝ) v.1 e + edgeSpin (K := ℝ) v.2.1 e +
            edgeSpin (K := ℝ) v.2.2.1 e + edgeSpin (K := ℝ) v.2.2.2 e) := by
    intro e _
    induction e using Sym2.ind with
    | _ i j =>
      rw [Fin.sum_univ_four]
      unfold uEdge edgeSpin
      simp only [Sym2.lift_mk]
      unfold uSite₁ uSite₂ uSite₃ uSite₄ u₁ u₂ u₃ u₄ siteQuadAt s₁ s₂ s₃ s₄
      ring
  rw [Finset.sum_congr rfl hedge]
  have hsite : ∑ i, p.β * p.h * uSite₁ i v
      = p.β * p.h * ∑ i, (Spin.sign ℝ (v.1 i) + Spin.sign ℝ (v.2.1 i) +
          Spin.sign ℝ (v.2.2.1 i) + Spin.sign ℝ (v.2.2.2 i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold uSite₁ u₁ siteQuadAt s₁ s₂ s₃ s₄
    ring
  rw [hsite]
  simp only [neg_mul]
  simp only [← Finset.mul_sum]
  have hsplit : ∑ x ∈ G.edgeFinset,
      (edgeSpin (K := ℝ) v.1 x + edgeSpin (K := ℝ) v.2.1 x +
        edgeSpin (K := ℝ) v.2.2.1 x + edgeSpin (K := ℝ) v.2.2.2 x)
      = (∑ x ∈ G.edgeFinset, edgeSpin (K := ℝ) v.1 x) +
        (∑ x ∈ G.edgeFinset, edgeSpin (K := ℝ) v.2.1 x) +
        (∑ x ∈ G.edgeFinset, edgeSpin (K := ℝ) v.2.2.1 x) +
        ∑ x ∈ G.edgeFinset, edgeSpin (K := ℝ) v.2.2.2 x := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hsplit' : ∑ x : ι,
      (Spin.sign ℝ (v.1 x) + Spin.sign ℝ (v.2.1 x) +
        Spin.sign ℝ (v.2.2.1 x) + Spin.sign ℝ (v.2.2.2 x))
      = (∑ x : ι, Spin.sign ℝ (v.1 x)) + (∑ x : ι, Spin.sign ℝ (v.2.1 x)) +
        (∑ x : ι, Spin.sign ℝ (v.2.2.1 x)) + ∑ x : ι, Spin.sign ℝ (v.2.2.2 x) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hsplit, hsplit']
  ring

omit [DecidableEq ι] in
/-- Every per-edge Hadamard product is a joint u-monomial (distinct endpoints). -/
theorem uEdge_eq_uMonomial {i j : ι} (hij : i ≠ j) (r : Fin 4) :
    ∃ k₀ l₀ m₀ n₀ : ι → ℕ, ∀ v : QuadConfig ι,
      uEdge r s(i, j) v = uMonomial k₀ l₀ m₀ n₀ v := by
  classical
  fin_cases r
  · exact ⟨_, _, _, _, fun v => (uMonomial_pair₁ hij v).symm⟩
  · exact ⟨_, _, _, _, fun v => (uMonomial_pair₂ hij v).symm⟩
  · exact ⟨_, _, _, _, fun v => (uMonomial_pair₃ hij v).symm⟩
  · exact ⟨_, _, _, _, fun v => (uMonomial_pair₄ hij v).symm⟩

/-- **The fourfold weight has non-negative u-moments** (ferromagnetic parameters): combine
the exponent identity with the exponential-of-sum closure. -/
theorem hasNonnegUMoments_quadWeight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    HasNonnegUMoments fun v => quadWeight G p v := by
  have hKedge : 0 ≤ p.β * p.J / 4 := by
    have := hf.hβ
    have := hf.hJ
    positivity
  have hKsite : 0 ≤ p.β * p.h := mul_nonneg hf.hβ.le hf.hh
  have hrw : (fun v => quadWeight G p v)
      = fun v => Real.exp (∑ er ∈ G.edgeFinset ×ˢ (Finset.univ : Finset (Fin 4)),
            p.β * p.J / 4 * uEdge er.2 er.1 v) *
          (Real.exp (∑ i, p.β * p.h * uSite₁ i v) * (fun _ => (1 : ℝ)) v) := by
    funext v
    rw [quadWeight_eq_exp]
    ring
  rw [hrw]
  refine hasNonnegUMoments_exp_sum_mul _ _ ?_
    (hasNonnegUMoments_exp_sum_mul _ _ ?_ hasNonnegUMoments_one)
  · -- edge terms are non-negative multiples of pair u-monomials
    rintro ⟨e, r⟩ her
    have he : e ∈ G.edgeFinset := (Finset.mem_product.mp her).1
    suffices h : ∃ (K : ℝ) (k₀ l₀ m₀ n₀ : ι → ℕ), 0 ≤ K ∧
        ∀ v, p.β * p.J / 4 * uEdge r e v = K * uMonomial k₀ l₀ m₀ n₀ v from h
    induction e using Sym2.ind with
    | _ i j =>
      have hadj : G.Adj i j := by
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      obtain ⟨k₀, l₀, m₀, n₀, heq⟩ := uEdge_eq_uMonomial hadj.ne r
      exact ⟨p.β * p.J / 4, k₀, l₀, m₀, n₀, hKedge, fun v => by rw [heq v]⟩
  · -- field terms are non-negative multiples of singleton u-monomials
    intro i _
    exact ⟨p.β * p.h, _, _, _, _, hKsite, fun v => by
      rw [uMonomial_single₁ i v]⟩

/-- **GJ Theorem 4.3.1 (Ising form)**: in the fourfold duplicate expectation, all joint
moments of the Hadamard variables are non-negative,
`0 ≤ ⟨u₁^A u₂^B u₃^C u₄^D⟩₄`, for ferromagnetic parameters. -/
theorem theorem_4_3_1 (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A B C D : Finset ι) :
    0 ≤ quadExpectation G p
      (fun v => uProd₁ A v * uProd₂ B v * uProd₃ C v * uProd₄ D v) := by
  unfold quadExpectation
  refine mul_nonneg (inv_nonneg.mpr (quadPartition_pos G p).le) ?_
  have hkey := hasNonnegUMoments_quadWeight G p hf
    (fun i => if i ∈ A then 1 else 0) (fun i => if i ∈ B then 1 else 0)
    (fun i => if i ∈ C then 1 else 0) (fun i => if i ∈ D then 1 else 0)
  simp_rw [uProd_eq_uMonomial] at hkey
  exact hkey

end Lebowitz

end IsingModel
