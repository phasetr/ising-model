import IsingModel.Inequalities.Lebowitz.DoubleSystem

/-!
# GJ Corollary 4.3.2: the Lebowitz t/q inequalities (GJ §4.3)

The three once-subtracted inequalities in the doubled `t`/`q` variables:
`0 ≤ ⟨t^A t^B⟩ − ⟨t^A⟩⟨t^B⟩`, `0 ≤ ⟨q^A q^B⟩ − ⟨q^A⟩⟨q^B⟩`, and
`0 ≤ ⟨t^A⟩⟨q^B⟩ − ⟨t^A q^B⟩`. Each difference lifts to a fourfold expectation of
`(all-plus factor) × (bracket)`; the `Finset.prod_add` subset expansion writes both as sums
of joint u-monomials with non-negative coefficients (the bracket coefficients are
`1 − (−1)^{|B∖T|} ∈ {0, 2}` — GJ's "ferromagnetic in the brackets"), and Theorem 4.3.1 makes
every term non-negative.

* `quadExpectation_sum` / `quadExpectation_sub` — linearity of the fourfold expectation.
* `tProd_fst_expand` etc. — the subset expansions of the rotated products.
* `cor_4_3_2_tt` / `cor_4_3_2_qq` / `cor_4_3_2_tq` — **GJ Corollary 4.3.2**.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.3,
Corollary 4.3.2, p. 60.
-/

namespace IsingModel

namespace Lebowitz

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The fourfold expectation commutes with finite sums of observables. -/
theorem quadExpectation_sum (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) {γ : Type*} (s : Finset γ) (F : γ → QuadConfig ι → ℝ) :
    quadExpectation G p (fun v => ∑ x ∈ s, F x v)
      = ∑ x ∈ s, quadExpectation G p (F x) := by
  unfold quadExpectation
  have h1 : ∀ v : QuadConfig ι, (∑ x ∈ s, F x v) * quadWeight G p v
      = ∑ x ∈ s, F x v * quadWeight G p v := fun v => Finset.sum_mul s (fun x => F x v) _
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.mul_sum]

/-- The fourfold expectation is homogeneous in scalar multiples. -/
theorem quadExpectation_const_mul (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (c : ℝ) (F : QuadConfig ι → ℝ) :
    quadExpectation G p (fun v => c * F v) = c * quadExpectation G p F := by
  unfold quadExpectation
  have h : ∑ v : QuadConfig ι, (c * F v) * quadWeight G p v
      = c * ∑ v : QuadConfig ι, F v * quadWeight G p v := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [h]
  ring

/-- The fourfold expectation respects subtraction of observables. -/
theorem quadExpectation_sub (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F H : QuadConfig ι → ℝ) :
    quadExpectation G p (fun v => F v - H v)
      = quadExpectation G p F - quadExpectation G p H := by
  unfold quadExpectation
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

/-- A product of negated factors picks up the sign `(−1)^{|s|}`. -/
theorem prod_neg_eq {γ : Type*} (s : Finset γ) (f : γ → ℝ) :
    ∏ i ∈ s, (-f i) = (-1 : ℝ) ^ s.card * ∏ i ∈ s, f i := by
  rw [show (fun i => -f i) = fun i => (-1 : ℝ) * f i from by funext i; ring,
    Finset.prod_mul_distrib, Finset.prod_const]

omit [Fintype ι] in
/-- **Subset expansion of the first-pair `t` product**:
`t^A(ξ,χ) = 2^{-|A|} ∑_{S ⊆ A} u₁^S u₂^{A∖S}`. -/
theorem tProd_fst_expand (A : Finset ι) (v : QuadConfig ι) :
    tProd A (v.1, v.2.1)
      = (1 / 2 : ℝ) ^ A.card *
        ∑ S ∈ A.powerset, uProd₁ S v * uProd₂ (A \ S) v := by
  unfold tProd uProd₁ uProd₂
  have hfac : ∀ i ∈ A, tSite i (v.1, v.2.1)
      = (1 / 2 : ℝ) * (uSite₁ i v + uSite₂ i v) := by
    intro i _
    rw [tSite_fst_eq]
    ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_add]

omit [Fintype ι] in
/-- **Subset expansion of the second-pair `t` product** (signs on the `u₂` part):
`t^A(ξ',χ') = 2^{-|A|} ∑_{S ⊆ A} (−1)^{|A∖S|} u₁^S u₂^{A∖S}`. -/
theorem tProd_snd_expand (A : Finset ι) (v : QuadConfig ι) :
    tProd A (v.2.2.1, v.2.2.2)
      = (1 / 2 : ℝ) ^ A.card *
        ∑ S ∈ A.powerset, (-1 : ℝ) ^ (A \ S).card * (uProd₁ S v * uProd₂ (A \ S) v) := by
  unfold tProd uProd₁ uProd₂
  have hfac : ∀ i ∈ A, tSite i (v.2.2.1, v.2.2.2)
      = (1 / 2 : ℝ) * (uSite₁ i v + -uSite₂ i v) := by
    intro i _
    rw [tSite_snd_eq]
    ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_add]
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [prod_neg_eq]
  ring

omit [Fintype ι] in
/-- **Subset expansion of the second-pair `q` product** (all-plus orientation):
`q^B(ξ',χ') = 2^{-|B|} ∑_{T ⊆ B} u₃^T u₄^{B∖T}`. -/
theorem qProd_snd_expand (B : Finset ι) (v : QuadConfig ι) :
    qProd B (v.2.2.1, v.2.2.2)
      = (1 / 2 : ℝ) ^ B.card *
        ∑ T ∈ B.powerset, uProd₃ T v * uProd₄ (B \ T) v := by
  unfold qProd uProd₃ uProd₄
  have hfac : ∀ i ∈ B, qSite i (v.2.2.1, v.2.2.2)
      = (1 / 2 : ℝ) * (uSite₃ i v + uSite₄ i v) := by
    intro i _
    rw [qSite_snd_eq]
    ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_add]

omit [Fintype ι] in
/-- **Subset expansion of the first-pair `q` product** (signs on the `u₄` part):
`q^B(ξ,χ) = 2^{-|B|} ∑_{T ⊆ B} (−1)^{|B∖T|} u₃^T u₄^{B∖T}`. -/
theorem qProd_fst_expand (B : Finset ι) (v : QuadConfig ι) :
    qProd B (v.1, v.2.1)
      = (1 / 2 : ℝ) ^ B.card *
        ∑ T ∈ B.powerset, (-1 : ℝ) ^ (B \ T).card * (uProd₃ T v * uProd₄ (B \ T) v) := by
  unfold qProd uProd₃ uProd₄
  have hfac : ∀ i ∈ B, qSite i (v.1, v.2.1)
      = (1 / 2 : ℝ) * (uSite₃ i v + -uSite₄ i v) := by
    intro i _
    rw [qSite_fst_eq]
    ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_add]
  congr 1
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [prod_neg_eq]
  ring

/-- **Joint u-monomial expectations are non-negative** (ferromagnetic parameters) — the
exponent-level form of Theorem 4.3.1. -/
theorem quadExpectation_uMonomial_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (k l m n : ι → ℕ) :
    0 ≤ quadExpectation G p (uMonomial k l m n) := by
  unfold quadExpectation
  exact mul_nonneg (inv_nonneg.mpr (quadPartition_pos G p).le)
    (hasNonnegUMoments_quadWeight G p hf k l m n)

/-- Products of two pairs of indicator u-products are joint u-monomials with non-negative
fourfold expectation. -/
theorem quadExpectation_uProd_pair_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (S S' T T' S₂ S₂' T₂ T₂' : Finset ι) :
    0 ≤ quadExpectation G p (fun v =>
      (uProd₁ S v * uProd₂ S' v * uProd₃ T v * uProd₄ T' v) *
        (uProd₁ S₂ v * uProd₂ S₂' v * uProd₃ T₂ v * uProd₄ T₂' v)) := by
  have hrw : (fun v : QuadConfig ι =>
      (uProd₁ S v * uProd₂ S' v * uProd₃ T v * uProd₄ T' v) *
        (uProd₁ S₂ v * uProd₂ S₂' v * uProd₃ T₂ v * uProd₄ T₂' v))
      = uMonomial
          ((fun i => if i ∈ S then 1 else 0) + fun i => if i ∈ S₂ then 1 else 0)
          ((fun i => if i ∈ S' then 1 else 0) + fun i => if i ∈ S₂' then 1 else 0)
          ((fun i => if i ∈ T then 1 else 0) + fun i => if i ∈ T₂ then 1 else 0)
          ((fun i => if i ∈ T' then 1 else 0) + fun i => if i ∈ T₂' then 1 else 0) := by
    funext v
    rw [← uMonomial_mul, uProd_eq_uMonomial, uProd_eq_uMonomial]
  rw [hrw]
  exact quadExpectation_uMonomial_nonneg G p hf _ _ _ _

/-- **Bracket expansion**: the generic algebraic identity behind all three Lebowitz
differences — a product of an all-plus expansion with a once-subtracted bracket is a double
sum with coefficients `cA·cB·(1 − z T)`. -/
theorem mul_bracket_expand {γ δ : Type*} (sA : Finset γ) (sB : Finset δ)
    (cA cB : ℝ) (X : γ → ℝ) (Y : δ → ℝ) (z : δ → ℝ) :
    (cA * ∑ S ∈ sA, X S) * (cB * ∑ T ∈ sB, Y T) -
      (cA * ∑ S ∈ sA, X S) * (cB * ∑ T ∈ sB, z T * Y T)
    = ∑ S ∈ sA, ∑ T ∈ sB, (cA * cB * (1 - z T)) * (X S * Y T) := by
  have h1 : (∑ S ∈ sA, X S) * (∑ T ∈ sB, Y T)
      = ∑ S ∈ sA, ∑ T ∈ sB, X S * Y T := Finset.sum_mul_sum sA sB X Y
  have h2 : (∑ S ∈ sA, X S) * (∑ T ∈ sB, z T * Y T)
      = ∑ S ∈ sA, ∑ T ∈ sB, X S * (z T * Y T) :=
    Finset.sum_mul_sum sA sB X fun T => z T * Y T
  have hLHS : (cA * ∑ S ∈ sA, X S) * (cB * ∑ T ∈ sB, Y T) -
      (cA * ∑ S ∈ sA, X S) * (cB * ∑ T ∈ sB, z T * Y T)
      = cA * cB * ((∑ S ∈ sA, X S) * (∑ T ∈ sB, Y T)
          - (∑ S ∈ sA, X S) * (∑ T ∈ sB, z T * Y T)) := by ring
  rw [hLHS, h1, h2, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  ring

/-- The double-sum coefficients of the bracket expansion are non-negative. -/
theorem bracket_coeff_nonneg (cardA cardB k : ℕ) :
    (0 : ℝ) ≤ (1 / 2) ^ cardA * (1 / 2) ^ cardB * (1 - (-1) ^ k) :=
  mul_nonneg (by positivity) (one_sub_neg_one_pow_nonneg k)

/-- The `t`/`q` mixed term is a joint u-monomial with non-negative fourfold expectation. -/
theorem quadExpectation_t_q_term_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (S S' T T' : Finset ι) :
    0 ≤ quadExpectation G p (fun v =>
      (uProd₁ S v * uProd₂ S' v) * (uProd₃ T v * uProd₄ T' v)) := by
  have hrw : (fun v : QuadConfig ι =>
      (uProd₁ S v * uProd₂ S' v) * (uProd₃ T v * uProd₄ T' v))
      = fun v => uProd₁ S v * uProd₂ S' v * uProd₃ T v * uProd₄ T' v := by
    funext v
    ring
  rw [hrw]
  have heq : (fun v : QuadConfig ι =>
      uProd₁ S v * uProd₂ S' v * uProd₃ T v * uProd₄ T' v)
      = uMonomial (fun i => if i ∈ S then 1 else 0) (fun i => if i ∈ S' then 1 else 0)
          (fun i => if i ∈ T then 1 else 0) (fun i => if i ∈ T' then 1 else 0) := by
    funext v
    rw [uProd_eq_uMonomial]
  rw [heq]
  exact quadExpectation_uMonomial_nonneg G p hf _ _ _ _

/-- The `t`/`t` (or `q`/`q`) doubled term is a joint u-monomial with non-negative fourfold
expectation. -/
theorem quadExpectation_t_t_term_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (S S' T T' : Finset ι) :
    0 ≤ quadExpectation G p (fun v =>
      (uProd₁ S v * uProd₂ S' v) * (uProd₁ T v * uProd₂ T' v)) := by
  have heq : (fun v : QuadConfig ι =>
      (uProd₁ S v * uProd₂ S' v) * (uProd₁ T v * uProd₂ T' v))
      = uMonomial
          ((fun i => if i ∈ S then 1 else 0) + fun i => if i ∈ T then 1 else 0)
          ((fun i => if i ∈ S' then 1 else 0) + fun i => if i ∈ T' then 1 else 0)
          ((fun i => if i ∈ (∅ : Finset ι) then 1 else 0) +
            fun i => if i ∈ (∅ : Finset ι) then 1 else 0)
          ((fun i => if i ∈ (∅ : Finset ι) then 1 else 0) +
            fun i => if i ∈ (∅ : Finset ι) then 1 else 0) := by
    funext v
    rw [← uMonomial_mul, uProd_eq_uMonomial, uProd_eq_uMonomial]
    unfold uProd₃ uProd₄
    rw [Finset.prod_empty, Finset.prod_empty]
    ring
  rw [heq]
  exact quadExpectation_uMonomial_nonneg G p hf _ _ _ _

/-- The `q`/`q` doubled term is a joint u-monomial with non-negative fourfold expectation. -/
theorem quadExpectation_q_q_term_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (S S' T T' : Finset ι) :
    0 ≤ quadExpectation G p (fun v =>
      (uProd₃ S v * uProd₄ S' v) * (uProd₃ T v * uProd₄ T' v)) := by
  have heq : (fun v : QuadConfig ι =>
      (uProd₃ S v * uProd₄ S' v) * (uProd₃ T v * uProd₄ T' v))
      = uMonomial
          ((fun i => if i ∈ (∅ : Finset ι) then 1 else 0) +
            fun i => if i ∈ (∅ : Finset ι) then 1 else 0)
          ((fun i => if i ∈ (∅ : Finset ι) then 1 else 0) +
            fun i => if i ∈ (∅ : Finset ι) then 1 else 0)
          ((fun i => if i ∈ S then 1 else 0) + fun i => if i ∈ T then 1 else 0)
          ((fun i => if i ∈ S' then 1 else 0) + fun i => if i ∈ T' then 1 else 0) := by
    funext v
    rw [← uMonomial_mul, uProd_eq_uMonomial, uProd_eq_uMonomial]
    unfold uProd₁ uProd₂
    rw [Finset.prod_empty, Finset.prod_empty]
    ring
  rw [heq]
  exact quadExpectation_uMonomial_nonneg G p hf _ _ _ _

/-- **GJ Corollary 4.3.2, third inequality**: `0 ≤ ⟨t^A⟩⟨q^B⟩ − ⟨t^A q^B⟩` for ferromagnetic
parameters. -/
theorem cor_4_3_2_tq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A B : Finset ι) :
    0 ≤ doubleExpectation G p (tProd A) * doubleExpectation G p (qProd B)
      - doubleExpectation G p (fun d => tProd A d * qProd B d) := by
  rw [← quadExpectation_factor_pair G p (tProd A) (qProd B),
    ← quadExpectation_fst_pair G p (fun d => tProd A d * qProd B d),
    ← quadExpectation_sub]
  have hpt : (fun v : QuadConfig ι =>
      tProd A (v.1, v.2.1) * qProd B (v.2.2.1, v.2.2.2)
        - tProd A (v.1, v.2.1) * qProd B (v.1, v.2.1))
      = fun v => ∑ S ∈ A.powerset, ∑ T ∈ B.powerset,
          ((1 / 2 : ℝ) ^ A.card * (1 / 2) ^ B.card * (1 - (-1) ^ (B \ T).card)) *
            ((uProd₁ S v * uProd₂ (A \ S) v) * (uProd₃ T v * uProd₄ (B \ T) v)) := by
    funext v
    rw [tProd_fst_expand, qProd_snd_expand, qProd_fst_expand]
    exact mul_bracket_expand A.powerset B.powerset _ _ _ _ _
  rw [hpt, quadExpectation_sum]
  refine Finset.sum_nonneg fun S _ => ?_
  rw [quadExpectation_sum]
  refine Finset.sum_nonneg fun T _ => ?_
  rw [quadExpectation_const_mul]
  exact mul_nonneg (bracket_coeff_nonneg _ _ _)
    (quadExpectation_t_q_term_nonneg G p hf _ _ _ _)

/-- **GJ Corollary 4.3.2, first inequality**: `0 ≤ ⟨t^A t^B⟩ − ⟨t^A⟩⟨t^B⟩` for ferromagnetic
parameters. -/
theorem cor_4_3_2_tt (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A B : Finset ι) :
    0 ≤ doubleExpectation G p (fun d => tProd A d * tProd B d)
      - doubleExpectation G p (tProd A) * doubleExpectation G p (tProd B) := by
  rw [← quadExpectation_factor_pair G p (tProd A) (tProd B),
    ← quadExpectation_fst_pair G p (fun d => tProd A d * tProd B d),
    ← quadExpectation_sub]
  have hpt : (fun v : QuadConfig ι =>
      tProd A (v.1, v.2.1) * tProd B (v.1, v.2.1)
        - tProd A (v.1, v.2.1) * tProd B (v.2.2.1, v.2.2.2))
      = fun v => ∑ S ∈ A.powerset, ∑ T ∈ B.powerset,
          ((1 / 2 : ℝ) ^ A.card * (1 / 2) ^ B.card * (1 - (-1) ^ (B \ T).card)) *
            ((uProd₁ S v * uProd₂ (A \ S) v) * (uProd₁ T v * uProd₂ (B \ T) v)) := by
    funext v
    rw [tProd_fst_expand A v, tProd_fst_expand B v, tProd_snd_expand B v]
    exact mul_bracket_expand A.powerset B.powerset _ _ _ _ _
  rw [hpt, quadExpectation_sum]
  refine Finset.sum_nonneg fun S _ => ?_
  rw [quadExpectation_sum]
  refine Finset.sum_nonneg fun T _ => ?_
  rw [quadExpectation_const_mul]
  exact mul_nonneg (bracket_coeff_nonneg _ _ _)
    (quadExpectation_t_t_term_nonneg G p hf _ _ _ _)

/-- **GJ Corollary 4.3.2, second inequality**: `0 ≤ ⟨q^A q^B⟩ − ⟨q^A⟩⟨q^B⟩` for ferromagnetic
parameters. -/
theorem cor_4_3_2_qq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A B : Finset ι) :
    0 ≤ doubleExpectation G p (fun d => qProd A d * qProd B d)
      - doubleExpectation G p (qProd A) * doubleExpectation G p (qProd B) := by
  have hsnd : doubleExpectation G p (fun d => qProd A d * qProd B d)
      = quadExpectation G p (fun v =>
          qProd A (v.2.2.1, v.2.2.2) * qProd B (v.2.2.1, v.2.2.2)) := by
    have h := quadExpectation_factor_pair G p (fun _ => 1)
      (fun d => qProd A d * qProd B d)
    have hone : doubleExpectation G p (fun _ => 1) = 1 := by
      unfold doubleExpectation
      rw [show ∑ d : DoubleConfig ι, (1 : ℝ) * doubleWeight G p d
          = doublePartition G p from by
        unfold doublePartition
        simp]
      field_simp [(doublePartition_pos G p).ne']
    rw [hone, one_mul] at h
    rw [← h]
    congr 1
    funext v
    ring
  have hfac : doubleExpectation G p (qProd A) * doubleExpectation G p (qProd B)
      = quadExpectation G p (fun v =>
          qProd B (v.1, v.2.1) * qProd A (v.2.2.1, v.2.2.2)) := by
    rw [quadExpectation_factor_pair G p (qProd B) (qProd A)]
    ring
  rw [hsnd, hfac, ← quadExpectation_sub]
  have hpt : (fun v : QuadConfig ι =>
      qProd A (v.2.2.1, v.2.2.2) * qProd B (v.2.2.1, v.2.2.2)
        - qProd B (v.1, v.2.1) * qProd A (v.2.2.1, v.2.2.2))
      = fun v => ∑ S ∈ A.powerset, ∑ T ∈ B.powerset,
          ((1 / 2 : ℝ) ^ A.card * (1 / 2) ^ B.card * (1 - (-1) ^ (B \ T).card)) *
            ((uProd₃ S v * uProd₄ (A \ S) v) * (uProd₃ T v * uProd₄ (B \ T) v)) := by
    funext v
    have hcomm : qProd B (v.1, v.2.1) * qProd A (v.2.2.1, v.2.2.2)
        = qProd A (v.2.2.1, v.2.2.2) * qProd B (v.1, v.2.1) := by ring
    rw [hcomm, qProd_snd_expand A v, qProd_snd_expand B v, qProd_fst_expand B v]
    exact mul_bracket_expand A.powerset B.powerset _ _ _ _ _
  rw [hpt, quadExpectation_sum]
  refine Finset.sum_nonneg fun S _ => ?_
  rw [quadExpectation_sum]
  refine Finset.sum_nonneg fun T _ => ?_
  rw [quadExpectation_const_mul]
  exact mul_nonneg (bracket_coeff_nonneg _ _ _)
    (quadExpectation_q_q_term_nonneg G p hf _ _ _ _)

end Lebowitz

end IsingModel
