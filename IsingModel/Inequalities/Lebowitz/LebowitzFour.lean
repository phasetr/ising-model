import IsingModel.Inequalities.Lebowitz.Cor432
import IsingModel.Inequalities.GHS.SpinFlip

/-!
# Discharging the four-point Lebowitz axiom at zero field (GJ §4.3)

The binomial translation of the doubled `t`/`q` products into per-copy spin products, the
generic powerset formulas for their doubled expectations in terms of correlations, and the
zero-field four-point Lebowitz inequality from `cor_4_3_2_tq` — replacing the
`lebowitz_four` axiom (whose only consumer is `cor_4_3_3` at `⟨J, 0, β⟩`; the general-field
statement is Lebowitz 1974 and is not consumed, and GJ's p. 61 partition-omission argument
itself uses `h = 0`).

* `tProd_expand` / `qProd_expand` — the binomial expansions on the doubled system.
* `doubleExpectation_sum` — finite-sum linearity.
* `doubleExpectation_spin_term` — per-term factorisation into correlation products.
* `doubleExpectation_tProd` / `_qProd` / `_tProd_mul_qProd` — the powerset formulas.
* `lebowitz_four_zero_field` — **the zero-field four-point Lebowitz inequality** (the
  axiom's shape at `h = 0`).

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.3,
Corollaries 4.3.2–4.3.3, pp. 60–61; J. L. Lebowitz, Comm. Math. Phys. 35 (1974).
-/

namespace IsingModel

namespace Lebowitz

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

omit [Fintype ι] in
/-- **Binomial expansion of the doubled `t` product**:
`t^A(ξ,χ) = ∑_{S ⊆ A} σ^S(ξ)·σ^{A∖S}(χ)`. -/
theorem tProd_expand (A : Finset ι) (d : DoubleConfig ι) :
    tProd A d = ∑ S ∈ A.powerset, spinProduct S d.1 * spinProduct (A \ S) d.2 := by
  unfold tProd tSite spinProduct
  have hfac : ∀ i ∈ A, Spin.sign ℝ (d.1 i) + Spin.sign ℝ (d.2 i)
      = ((↑(d.1 i).toSign : ℝ)) + ((↑(d.2 i).toSign : ℝ)) := by
    intro i _
    rfl
  rw [Finset.prod_congr rfl hfac, Finset.prod_add]

omit [Fintype ι] in
/-- **Binomial expansion of the doubled `q` product** (signs on the second copy):
`q^B(ξ,χ) = ∑_{T ⊆ B} (−1)^{|B∖T|} σ^T(ξ)·σ^{B∖T}(χ)`. -/
theorem qProd_expand (B : Finset ι) (d : DoubleConfig ι) :
    qProd B d = ∑ T ∈ B.powerset,
      (-1 : ℝ) ^ (B \ T).card * (spinProduct T d.1 * spinProduct (B \ T) d.2) := by
  unfold qProd qSite spinProduct
  have hfac : ∀ i ∈ B, Spin.sign ℝ (d.1 i) - Spin.sign ℝ (d.2 i)
      = ((↑(d.1 i).toSign : ℝ)) + -((↑(d.2 i).toSign : ℝ)) := by
    intro i _
    have : Spin.sign ℝ (d.1 i) = ((↑(d.1 i).toSign : ℝ)) := rfl
    have : Spin.sign ℝ (d.2 i) = ((↑(d.2 i).toSign : ℝ)) := rfl
    simp [Spin.sign]
    ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [prod_neg_eq]
  ring

/-- The doubled expectation commutes with finite sums of observables. -/
theorem doubleExpectation_sum (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) {γ : Type*} (s : Finset γ) (F : γ → DoubleConfig ι → ℝ) :
    doubleExpectation G p (fun d => ∑ x ∈ s, F x d)
      = ∑ x ∈ s, doubleExpectation G p (F x) := by
  unfold doubleExpectation
  have h1 : ∀ d : DoubleConfig ι, (∑ x ∈ s, F x d) * doubleWeight G p d
      = ∑ x ∈ s, F x d * doubleWeight G p d := fun d => Finset.sum_mul s (fun x => F x d) _
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.mul_sum]

/-- The doubled expectation is homogeneous in scalar multiples. -/
theorem doubleExpectation_const_mul (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (c : ℝ) (F : DoubleConfig ι → ℝ) :
    doubleExpectation G p (fun d => c * F d) = c * doubleExpectation G p F := by
  unfold doubleExpectation
  have h : ∑ d : DoubleConfig ι, (c * F d) * doubleWeight G p d
      = c * ∑ d : DoubleConfig ι, F d * doubleWeight G p d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [h]
  ring

/-- **Per-term factorisation**: the doubled expectation of a per-copy spin-product pair is
the product of the correlations. -/
theorem doubleExpectation_spin_term (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (X Y : Finset ι) :
    doubleExpectation G p (fun d => spinProduct X d.1 * spinProduct Y d.2)
      = correlation G p X * correlation G p Y := by
  rw [doubleExpectation_factor]
  rfl

/-- **Powerset formula for the doubled `t` expectation**:
`⟨t^A⟩₂ = ∑_{S ⊆ A} c_S · c_{A∖S}`. -/
theorem doubleExpectation_tProd (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A : Finset ι) :
    doubleExpectation G p (tProd A)
      = ∑ S ∈ A.powerset, correlation G p S * correlation G p (A \ S) := by
  have hrw : tProd (ι := ι) A
      = fun d => ∑ S ∈ A.powerset, spinProduct S d.1 * spinProduct (A \ S) d.2 := by
    funext d
    exact tProd_expand A d
  rw [hrw, doubleExpectation_sum]
  exact Finset.sum_congr rfl fun S _ => doubleExpectation_spin_term G p S (A \ S)

/-- **Powerset formula for the doubled `q` expectation**:
`⟨q^B⟩₂ = ∑_{T ⊆ B} (−1)^{|B∖T|} c_T · c_{B∖T}`. -/
theorem doubleExpectation_qProd (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (B : Finset ι) :
    doubleExpectation G p (qProd B)
      = ∑ T ∈ B.powerset,
          (-1 : ℝ) ^ (B \ T).card * (correlation G p T * correlation G p (B \ T)) := by
  have hrw : qProd (ι := ι) B
      = fun d => ∑ T ∈ B.powerset,
          (-1 : ℝ) ^ (B \ T).card * (spinProduct T d.1 * spinProduct (B \ T) d.2) := by
    funext d
    exact qProd_expand B d
  rw [hrw, doubleExpectation_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [doubleExpectation_const_mul, doubleExpectation_spin_term]

/-- **Powerset formula for the doubled `t·q` expectation** (disjoint index sets):
`⟨t^A q^B⟩₂ = ∑_{S ⊆ A} ∑_{T ⊆ B} (−1)^{|B∖T|} c_{S∪T} · c_{(A∖S)∪(B∖T)}`. -/
theorem doubleExpectation_tProd_mul_qProd (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A B : Finset ι) (hAB : Disjoint A B) :
    doubleExpectation G p (fun d => tProd A d * qProd B d)
      = ∑ S ∈ A.powerset, ∑ T ∈ B.powerset,
          (-1 : ℝ) ^ (B \ T).card *
            (correlation G p (S ∪ T) * correlation G p ((A \ S) ∪ (B \ T))) := by
  have hobs : (fun d : DoubleConfig ι => tProd A d * qProd B d)
      = fun d => ∑ S ∈ A.powerset, ∑ T ∈ B.powerset,
          (-1 : ℝ) ^ (B \ T).card *
            (spinProduct (S ∪ T) d.1 * spinProduct ((A \ S) ∪ (B \ T)) d.2) := by
    funext d
    rw [tProd_expand A d, qProd_expand B d, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun S hS => Finset.sum_congr rfl fun T hT => ?_
    have hS' : S ⊆ A := Finset.mem_powerset.mp hS
    have hT' : T ⊆ B := Finset.mem_powerset.mp hT
    have hd₁ : Disjoint S T := hAB.mono hS' hT'
    have hd₂ : Disjoint (A \ S) (B \ T) :=
      hAB.mono (Finset.sdiff_subset) (Finset.sdiff_subset)
    have hm₁ : spinProduct S d.1 * spinProduct T d.1 = spinProduct (S ∪ T) d.1 := by
      rw [spinProduct_mul, hd₁.symmDiff_eq_sup]
      rfl
    have hm₂ : spinProduct (A \ S) d.2 * spinProduct (B \ T) d.2
        = spinProduct ((A \ S) ∪ (B \ T)) d.2 := by
      rw [spinProduct_mul, hd₂.symmDiff_eq_sup]
      rfl
    calc (spinProduct S d.1 * spinProduct (A \ S) d.2) *
          ((-1 : ℝ) ^ (B \ T).card * (spinProduct T d.1 * spinProduct (B \ T) d.2))
        = (-1 : ℝ) ^ (B \ T).card *
            ((spinProduct S d.1 * spinProduct T d.1) *
              (spinProduct (A \ S) d.2 * spinProduct (B \ T) d.2)) := by ring
      _ = (-1 : ℝ) ^ (B \ T).card *
            (spinProduct (S ∪ T) d.1 * spinProduct ((A \ S) ∪ (B \ T)) d.2) := by
          rw [hm₁, hm₂]
  rw [hobs, doubleExpectation_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [doubleExpectation_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [doubleExpectation_const_mul, doubleExpectation_spin_term]

omit [Fintype ι] in
/-- Powerset of a pair, summed: `∑_{S ⊆ {a,b}} f S = f ∅ + f {a} + f {b} + f {a,b}`. -/
theorem sum_powerset_pair {a b : ι} (hab : a ≠ b) (f : Finset ι → ℝ) :
    ∑ S ∈ ({a, b} : Finset ι).powerset, f S = f ∅ + f {a} + f {b} + f {a, b} := by
  rw [show ({a, b} : Finset ι) = insert a {b} from rfl,
    Finset.sum_powerset_insert (by simp [hab]),
    show ({b} : Finset ι) = insert b ∅ from rfl,
    Finset.sum_powerset_insert (by simp),
    Finset.sum_powerset_insert (by simp)]
  simp only [Finset.powerset_empty, Finset.sum_singleton]
  have h1 : insert a (∅ : Finset ι) = {a} := rfl
  have h2 : insert b (∅ : Finset ι) = {b} := rfl
  have h3 : insert a ({b} : Finset ι) = {a, b} := rfl
  rw [h1, h2, h3]
  ring

omit [Fintype ι] in
/-- Removing one element of a pair leaves the other. -/
theorem pair_sdiff_left {a b : ι} (hab : a ≠ b) :
    ({a, b} : Finset ι) \ {a} = {b} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx | hx, hxa⟩
    · exact absurd hx hxa
    · exact hx
  · rintro rfl
    exact ⟨Or.inr rfl, fun h => hab h.symm⟩

omit [Fintype ι] in
/-- Removing the other element of a pair leaves the first. -/
theorem pair_sdiff_right {a b : ι} (hab : a ≠ b) :
    ({a, b} : Finset ι) \ {b} = {a} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx | hx, hxb⟩
    · exact hx
    · exact absurd hx hxb
  · rintro rfl
    exact ⟨Or.inl rfl, fun h => hab h⟩

/-- **The zero-field four-point Lebowitz inequality** (equivalent to `U₄ ≤ 0`):
`⟨σ_iσ_jσ_kσ_l⟩ ≤ ⟨σ_iσ_j⟩⟨σ_kσ_l⟩ + ⟨σ_iσ_k⟩⟨σ_jσ_l⟩ + ⟨σ_iσ_l⟩⟨σ_jσ_k⟩` for ferromagnetic
parameters at `h = 0`. This is the corrected replacement of the former `lebowitz_four`
axiom: the axiom's stated form specialised at `h = 0` to the false bound
`U₄ ≤ −2⟨σ_iσ_j⟩⟨σ_kσ_l⟩` (counterexample: two disjoint strongly coupled edges with
vanishing cross-correlations). The proof applies `cor_4_3_2_tq` with `A = {i,j}`,
`B = {k,l}`, evaluates the powerset formulas over the two pairs, and kills the odd
correlations by the zero-field spin-flip symmetry. -/
theorem lebowitz_four_zero_field (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    correlation G ⟨J, 0, β⟩ {i, j, k, l}
      ≤ correlation G ⟨J, 0, β⟩ {i, j} * correlation G ⟨J, 0, β⟩ {k, l}
        + correlation G ⟨J, 0, β⟩ {i, k} * correlation G ⟨J, 0, β⟩ {j, l}
        + correlation G ⟨J, 0, β⟩ {i, l} * correlation G ⟨J, 0, β⟩ {j, k} := by
  have htq := cor_4_3_2_tq G ⟨J, 0, β⟩ hf {i, j} {k, l}
  rw [doubleExpectation_tProd, doubleExpectation_qProd,
    doubleExpectation_tProd_mul_qProd G _ {i, j} {k, l}
      (by simp [Finset.disjoint_left, hik, hil, hjk, hjl])] at htq
  simp only [sum_powerset_pair hij, sum_powerset_pair hkl] at htq
  -- normalise the set expressions
  simp only [Finset.sdiff_empty, Finset.sdiff_self, pair_sdiff_left hij,
    pair_sdiff_right hij, pair_sdiff_left hkl, pair_sdiff_right hkl,
    Finset.empty_union, Finset.union_empty, Finset.singleton_union,
    Finset.insert_union, Finset.card_empty, Finset.card_singleton] at htq
  -- cardinality of the pair
  have hcard_kl : ({k, l} : Finset ι).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hkl]), Finset.card_singleton]
  rw [hcard_kl] at htq
  norm_num at htq
  -- zero-field odd correlations vanish
  have hv_i : correlation G ⟨J, 0, β⟩ {i} = 0 :=
    correlation_odd_vanish G J β {i} ⟨0, by simp⟩
  have hv_j : correlation G ⟨J, 0, β⟩ {j} = 0 :=
    correlation_odd_vanish G J β {j} ⟨0, by simp⟩
  have hv_k : correlation G ⟨J, 0, β⟩ {k} = 0 :=
    correlation_odd_vanish G J β {k} ⟨0, by simp⟩
  have hv_l : correlation G ⟨J, 0, β⟩ {l} = 0 :=
    correlation_odd_vanish G J β {l} ⟨0, by simp⟩
  have hv_ijk : correlation G ⟨J, 0, β⟩ {i, j, k} = 0 :=
    correlation_odd_vanish G J β {i, j, k} ⟨1, by
      simp [Finset.card_insert_of_notMem, hij, hik, hjk]⟩
  have hv_ijl : correlation G ⟨J, 0, β⟩ {i, j, l} = 0 :=
    correlation_odd_vanish G J β {i, j, l} ⟨1, by
      simp [Finset.card_insert_of_notMem, hij, hil, hjl]⟩
  have hv_ikl : correlation G ⟨J, 0, β⟩ {i, k, l} = 0 :=
    correlation_odd_vanish G J β {i, k, l} ⟨1, by
      simp [Finset.card_insert_of_notMem, hik, hil, hkl]⟩
  have hv_jkl : correlation G ⟨J, 0, β⟩ {j, k, l} = 0 :=
    correlation_odd_vanish G J β {j, k, l} ⟨1, by
      simp [Finset.card_insert_of_notMem, hjk, hjl, hkl]⟩
  rw [hv_i, hv_j, hv_k, hv_l, hv_ijk, hv_ijl, hv_ikl, hv_jkl] at htq
  -- the surviving terms give the inequality
  nlinarith [htq]

end Lebowitz

end IsingModel
