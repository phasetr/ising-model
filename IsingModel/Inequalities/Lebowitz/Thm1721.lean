import IsingModel.Inequalities.Lebowitz.LebowitzFour
import IsingModel.Inequalities.GKS

/-!
# GJ Theorem 17.2.1: general odd-subset correlation bound (GJ §17.2, p. 305)

For a ferromagnetic Ising model at zero external field, with `A`, `B` disjoint finite
site sets of even cardinality, the once-subtracted correlation is bounded above by the
ordered odd-subset sum

`⟨φ^{A∪B}⟩ − ⟨φ^A⟩⟨φ^B⟩ ≤
    ∑_{A₁ ⊆ A, |A₁| odd} ∑_{B₁ ⊆ B, |B₁| odd} ⟨φ^{A₁∪B₁}⟩ ⟨φ^{(A∖A₁)∪(B∖B₁)}⟩`.

This is the lattice reading of Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987),
Theorem 17.2.1, p. 305, whose one-line proof invokes Corollary 4.3.3 (pp. 61–62) and
removes the lattice and volume cutoffs.  This Lean formalization stays at the
finite-volume / finite-`Λ` level and does not perform GJ's cutoff removal; the general
inequality is established for finite index types (`SimpleGraph`, `Λ`-induced), matching
the existing 4-point convention (`cor_4_3_3`).  The direction of the inequality is `≤` (an
upper bound); the surface OCR of the master text renders it as `≥`, but the book means
`≤` (it restates the *upper* half of Cor. 4.3.3, and Cor. 17.2.2 consumes it as an
upper bound).

The proof route is the p. 61–62 reduction:

* start from Corollary 4.3.2's third inequality `⟨t^A q^B⟩₂ ≤ ⟨t^A⟩₂⟨q^B⟩₂`
  (`cor_4_3_2_tq`);
* expand both sides by the powerset formulas (`doubleExpectation_tProd` / `_qProd` /
  `_tProd_mul_qProd`, the last one using `Disjoint A B`), giving a signed double
  powerset sum `∑_{S⊆A}∑_{T⊆B} (−1)^{|B∖T|}(L−R) ≤ 0` with `L = c_{S∪T}c_{(A∖S)∪(B∖T)}`,
  `R = c_S c_{A∖S} c_T c_{B∖T}`;
* bound this signed sum below by a comparison term (`reductionTarget`) that equals
  `2(c_{A∪B} − c_A c_B) − S`, using the per-partition Griffiths-II discard
  `R ≤ L` (`correlation_prod_pair_ge`) for the even terms and the zero-field
  odd-cardinality vanishing (`correlation_odd_vanish`) for the odd terms.

The two surviving trivial partitions `(A,B)` and `(∅,∅)` each contribute
`c_{A∪B} − c_A c_B`, giving the factor `2` in the core estimate
`2(c_{A∪B} − c_A c_B) ≤ S` (`two_mul_correlation_union_sub_le`).  The literal
Theorem 17.2.1 (`thm_17_2_1`) follows since `S ≥ 0`.

## Main results

* `correlation_prod_pair_ge` — the per-partition discard inequality `R ≤ L`.
* `two_mul_correlation_union_sub_le` — the core estimate `2(c_{A∪B} − c_A c_B) ≤ S`
  (the sharp form, equivalent to Corollary 4.3.3's unordered bound).
* `thm_17_2_1` — **GJ Theorem 17.2.1**, `c_{A∪B} − c_A c_B ≤ S`.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), Theorem 17.2.1,
p. 305; Corollary 4.3.3, pp. 61–62.
-/

namespace IsingModel

namespace Lebowitz

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- **Per-partition Griffiths-II discard inequality**: for disjoint pairs `(S, T)` and
`(U, V)`, the disconnected product of four correlations is bounded above by the product
of the two merged correlations,
`c_S c_U c_T c_V ≤ c_{S∪T} c_{U∪V}`.  This is the `R ≤ L` (`D ≥ 0`) step of the
Glimm–Jaffe p. 61–62 reduction: two applications of GKS-II (`gks_second`) on the
disjoint mergers `S ⊔ T` and `U ⊔ V`, combined by non-negativity of correlations
(`gks_first`). -/
theorem correlation_prod_pair_ge (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (S T U V : Finset ι)
    (hST : Disjoint S T) (hUV : Disjoint U V) :
    correlation G p S * correlation G p U * correlation G p T * correlation G p V
      ≤ correlation G p (S ∪ T) * correlation G p (U ∪ V) := by
  have h1 : correlation G p S * correlation G p T ≤ correlation G p (S ∪ T) := by
    have h := gks_second G p hf S T
    rwa [hST.symmDiff_eq_sup, Finset.sup_eq_union] at h
  have h2 : correlation G p U * correlation G p V ≤ correlation G p (U ∪ V) := by
    have h := gks_second G p hf U V
    rwa [hUV.symmDiff_eq_sup, Finset.sup_eq_union] at h
  have hUVnn : 0 ≤ correlation G p U * correlation G p V :=
    mul_nonneg (gks_first G p hf U) (gks_first G p hf V)
  have hSTnn : 0 ≤ correlation G p (S ∪ T) := gks_first G p hf (S ∪ T)
  calc correlation G p S * correlation G p U * correlation G p T * correlation G p V
      = (correlation G p S * correlation G p T) * (correlation G p U * correlation G p V) := by
        ring
    _ ≤ correlation G p (S ∪ T) * correlation G p (U ∪ V) := mul_le_mul h1 h2 hUVnn hSTnn

/-- The signed summand of the expanded Corollary 4.3.2 inequality,
`(−1)^{|B∖T|}(c_{S∪T}c_{(A∖S)∪(B∖T)} − c_S c_{A∖S} c_T c_{B∖T})`.  Its double powerset
sum is `≤ 0` (from `cor_4_3_2_tq`). -/
private noncomputable def reductionSummand (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ)
    (A B S T : Finset ι) : ℝ :=
  (-1 : ℝ) ^ (B \ T).card *
    (correlation G ⟨J, 0, β⟩ (S ∪ T) * correlation G ⟨J, 0, β⟩ ((A \ S) ∪ (B \ T))
      - correlation G ⟨J, 0, β⟩ S * correlation G ⟨J, 0, β⟩ (A \ S)
          * correlation G ⟨J, 0, β⟩ T * correlation G ⟨J, 0, β⟩ (B \ T))

/-- The per-partition comparison term used to bound `reductionSummand` from below.  Its
double powerset sum equals `2(c_{A∪B} − c_A c_B) − S`, where `S` is the target
odd-subset sum: the two trivial partitions `(A,B)` and `(∅,∅)` each contribute
`c_{A∪B} − c_A c_B`, and the odd–odd partitions contribute `−c_{S∪T}c_{(A∖S)∪(B∖T)}`. -/
private noncomputable def reductionTarget (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ)
    (A B S T : Finset ι) : ℝ :=
  (if S = A ∧ T = B then
      correlation G ⟨J, 0, β⟩ (A ∪ B)
        - correlation G ⟨J, 0, β⟩ A * correlation G ⟨J, 0, β⟩ B else 0)
  + (if S = ∅ ∧ T = ∅ then
      correlation G ⟨J, 0, β⟩ (A ∪ B)
        - correlation G ⟨J, 0, β⟩ A * correlation G ⟨J, 0, β⟩ B else 0)
  - (if Odd S.card ∧ Odd T.card then
      correlation G ⟨J, 0, β⟩ (S ∪ T) * correlation G ⟨J, 0, β⟩ ((A \ S) ∪ (B \ T)) else 0)

/-- **Termwise comparison**: for every partition `(S ⊆ A, T ⊆ B)`, the comparison term
is `≤` the signed summand.  This is the local heart of the p. 61–62 reduction, split by
the parities of `|T|` (equivalently `|B∖T|`, the sign) and `|S|`. -/
private theorem reductionTarget_le_summand (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ)) (A B : Finset ι)
    (hAB : Disjoint A B) (_hA : Even A.card) (hB : Even B.card)
    (S T : Finset ι) (hS : S ⊆ A) (hT : T ⊆ B) :
    reductionTarget G J β A B S T ≤ reductionSummand G J β A B S T := by
  simp only [reductionTarget, reductionSummand]
  have hST : Disjoint S T := hAB.mono hS hT
  have hUV : Disjoint (A \ S) (B \ T) :=
    hAB.mono Finset.sdiff_subset Finset.sdiff_subset
  by_cases hTo : Odd T.card
  · -- `|B∖T|` odd: sign `= −1`, `c_{B∖T} = 0`; trivial partitions excluded.
    have hko : Odd (B \ T).card := by
      have hBeven : Even ((B \ T).card + T.card) := by
        rw [Finset.card_sdiff_add_card_eq_card hT]; exact hB
      rw [Nat.even_add] at hBeven
      rw [← Nat.not_even_iff_odd]
      exact fun hev => (Nat.not_even_iff_odd.mpr hTo) (hBeven.mp hev)
    have cBT0 : correlation G ⟨J, 0, β⟩ (B \ T) = 0 :=
      correlation_odd_vanish G J β _ hko
    have hnotAB : ¬ (S = A ∧ T = B) := by
      rintro ⟨_, hTB⟩; rw [hTB] at hTo; exact (Nat.not_even_iff_odd.mpr hTo) hB
    have hnotEmpty : ¬ (S = ∅ ∧ T = ∅) := by
      rintro ⟨_, hTe0⟩; rw [hTe0] at hTo; simp at hTo
    rw [if_neg hnotAB, if_neg hnotEmpty, Odd.neg_one_pow hko, cBT0]
    by_cases hSo : Odd S.card
    · rw [if_pos ⟨hSo, hTo⟩]; apply le_of_eq; ring
    · have hSe : Even S.card := Nat.not_odd_iff_even.mp hSo
      have hSTcard : (S ∪ T).card = S.card + T.card := Finset.card_union_of_disjoint hST
      have hSTodd : Odd (S ∪ T).card := by rw [hSTcard]; exact hSe.add_odd hTo
      have hcST0 : correlation G ⟨J, 0, β⟩ (S ∪ T) = 0 :=
        correlation_odd_vanish G J β _ hSTodd
      rw [if_neg (fun h => hSo h.1), hcST0]; apply le_of_eq; ring
  · -- `|B∖T|` even: sign `= 1`, so the summand is `L − R`.
    have hTe : Even T.card := Nat.not_odd_iff_even.mp hTo
    have hke : Even (B \ T).card := by
      have hBeven : Even ((B \ T).card + T.card) := by
        rw [Finset.card_sdiff_add_card_eq_card hT]; exact hB
      rw [Nat.even_add] at hBeven
      exact hBeven.mpr hTe
    rw [Even.neg_one_pow hke, one_mul,
      if_neg (show ¬(Odd S.card ∧ Odd T.card) from fun h => hTo h.2)]
    by_cases h2 : S = ∅ ∧ T = ∅
    · by_cases h1 : S = A ∧ T = B
      · -- both trivial: forces `A = B = ∅`, everything vanishes.
        have hAe : A = ∅ := h1.1 ▸ h2.1
        have hBe : B = ∅ := h1.2 ▸ h2.2
        rw [if_pos h1, if_pos h2, h2.1, h2.2, hAe, hBe]
        simp [correlation_empty]
      · rw [if_neg h1, if_pos h2, h2.1, h2.2]
        simp only [Finset.empty_union, Finset.sdiff_empty, correlation_empty, one_mul, mul_one]
        linarith
    · by_cases h1 : S = A ∧ T = B
      · rw [if_pos h1, if_neg h2, h1.1, h1.2]
        simp only [Finset.sdiff_self, Finset.empty_union, correlation_empty, mul_one]
        linarith
      · rw [if_neg h1, if_neg h2]
        have hge := correlation_prod_pair_ge G ⟨J, 0, β⟩ hf S T (A \ S) (B \ T) hST hUV
        linarith

/-- **Core estimate (sharp form)**: `2(c_{A∪B} − c_A c_B) ≤ S`.  Both trivial partitions
survive with sign `+1`, producing the factor `2`; the even nontrivial partitions are
Griffiths-II non-negative and are discarded from the upper bound, and the odd
partitions assemble into `S`.  This is equivalent to Corollary 4.3.3's unordered bound
`c_{A∪B} − c_A c_B ≤ S/2`. -/
theorem two_mul_correlation_union_sub_le (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ)) (A B : Finset ι)
    (hAB : Disjoint A B) (hA : Even A.card) (hB : Even B.card) :
    2 * (correlation G ⟨J, 0, β⟩ (A ∪ B)
          - correlation G ⟨J, 0, β⟩ A * correlation G ⟨J, 0, β⟩ B)
      ≤ ∑ A₁ ∈ A.powerset.filter (fun s => Odd s.card),
          ∑ B₁ ∈ B.powerset.filter (fun s => Odd s.card),
            correlation G ⟨J, 0, β⟩ (A₁ ∪ B₁)
              * correlation G ⟨J, 0, β⟩ ((A \ A₁) ∪ (B \ B₁)) := by
  -- Step 1: the signed double sum is `≤ 0` (`cor_4_3_2_tq`, expanded).
  have hf_sum : ∑ S ∈ A.powerset, ∑ T ∈ B.powerset, reductionSummand G J β A B S T ≤ 0 := by
    have hexp := cor_4_3_2_tq G ⟨J, 0, β⟩ hf A B
    rw [doubleExpectation_tProd, doubleExpectation_qProd,
        doubleExpectation_tProd_mul_qProd G ⟨J, 0, β⟩ A B hAB, Finset.sum_mul_sum,
        ← Finset.sum_sub_distrib] at hexp
    have hrw : ∀ S ∈ A.powerset,
        (∑ T ∈ B.powerset, correlation G ⟨J, 0, β⟩ S * correlation G ⟨J, 0, β⟩ (A \ S)
              * ((-1 : ℝ) ^ (B \ T).card
                * (correlation G ⟨J, 0, β⟩ T * correlation G ⟨J, 0, β⟩ (B \ T))))
          - (∑ T ∈ B.powerset, (-1 : ℝ) ^ (B \ T).card
                * (correlation G ⟨J, 0, β⟩ (S ∪ T)
                    * correlation G ⟨J, 0, β⟩ ((A \ S) ∪ (B \ T))))
        = ∑ T ∈ B.powerset, - reductionSummand G J β A B S T := by
      intro S _
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun T _ => ?_
      simp only [reductionSummand]; ring
    rw [Finset.sum_congr rfl hrw] at hexp
    simp only [Finset.sum_neg_distrib] at hexp
    linarith
  -- Step 2: the comparison sum is `≤` the signed double sum, termwise.
  have htarget_le : ∑ S ∈ A.powerset, ∑ T ∈ B.powerset, reductionTarget G J β A B S T
      ≤ ∑ S ∈ A.powerset, ∑ T ∈ B.powerset, reductionSummand G J β A B S T := by
    refine Finset.sum_le_sum fun S hS => Finset.sum_le_sum fun T hT => ?_
    exact reductionTarget_le_summand G J β hf A B hAB hA hB S T
      (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT)
  -- Step 3: the comparison sum equals `2(c_{A∪B} − c_A c_B) − S`.
  have hpoint : ∀ (a b : Finset ι) (v : ℝ), a ∈ A.powerset → b ∈ B.powerset →
      (∑ S ∈ A.powerset, ∑ T ∈ B.powerset, (if S = a ∧ T = b then v else 0)) = v := by
    intro a b v ha hb
    rw [Finset.sum_eq_single_of_mem a ha]
    · rw [Finset.sum_eq_single_of_mem b hb]
      · simp
      · intro T _ hTb; simp [hTb]
    · intro S _ hSa; exact Finset.sum_eq_zero fun T _ => by simp [hSa]
  have htarget_eq :
      ∑ S ∈ A.powerset, ∑ T ∈ B.powerset, reductionTarget G J β A B S T
        = 2 * (correlation G ⟨J, 0, β⟩ (A ∪ B)
              - correlation G ⟨J, 0, β⟩ A * correlation G ⟨J, 0, β⟩ B)
          - ∑ A₁ ∈ A.powerset.filter (fun s => Odd s.card),
              ∑ B₁ ∈ B.powerset.filter (fun s => Odd s.card),
                correlation G ⟨J, 0, β⟩ (A₁ ∪ B₁)
                  * correlation G ⟨J, 0, β⟩ ((A \ A₁) ∪ (B \ B₁)) := by
    have hite1 := hpoint A B
      (correlation G ⟨J, 0, β⟩ (A ∪ B)
        - correlation G ⟨J, 0, β⟩ A * correlation G ⟨J, 0, β⟩ B)
      (Finset.mem_powerset.mpr (Finset.Subset.refl A))
      (Finset.mem_powerset.mpr (Finset.Subset.refl B))
    have hite2 := hpoint ∅ ∅
      (correlation G ⟨J, 0, β⟩ (A ∪ B)
        - correlation G ⟨J, 0, β⟩ A * correlation G ⟨J, 0, β⟩ B)
      (Finset.mem_powerset.mpr (Finset.empty_subset A))
      (Finset.mem_powerset.mpr (Finset.empty_subset B))
    have hite3 :
        (∑ S ∈ A.powerset, ∑ T ∈ B.powerset,
            (if Odd S.card ∧ Odd T.card then
              correlation G ⟨J, 0, β⟩ (S ∪ T)
                * correlation G ⟨J, 0, β⟩ ((A \ S) ∪ (B \ T)) else 0))
          = ∑ A₁ ∈ A.powerset.filter (fun s => Odd s.card),
              ∑ B₁ ∈ B.powerset.filter (fun s => Odd s.card),
                correlation G ⟨J, 0, β⟩ (A₁ ∪ B₁)
                  * correlation G ⟨J, 0, β⟩ ((A \ A₁) ∪ (B \ B₁)) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [Finset.sum_filter]
      by_cases hSo : Odd S.card
      · simp only [hSo, true_and, if_true]
      · simp only [hSo, false_and, if_false, Finset.sum_const_zero]
    simp only [reductionTarget, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hite1, hite2, hite3]; ring
  linarith

/-- **Glimm–Jaffe Theorem 17.2.1** (general odd-subset correlation bound, GJ §17.2,
p. 305).  For a ferromagnetic Ising model at zero external field, with `A`, `B` disjoint
finite site sets of even cardinality,

`⟨φ^{A∪B}⟩ − ⟨φ^A⟩⟨φ^B⟩ ≤
    ∑_{A₁ ⊆ A, |A₁| odd} ∑_{B₁ ⊆ B, |B₁| odd} ⟨φ^{A₁∪B₁}⟩ ⟨φ^{(A∖A₁)∪(B∖B₁)}⟩`.

The `Disjoint A B` hypothesis is the faithful Ising specialisation of Glimm–Jaffe's
continuum `φ⁴` statement (on the lattice `σ² = 1`, overlapping products would collapse
to a symmetric difference).  The bound follows from the core estimate
`two_mul_correlation_union_sub_le` together with `S ≥ 0`; it is the weaker (ordered,
factor-`2`) form and does not subsume the sharp four-point Corollary 4.3.3. -/
theorem thm_17_2_1 (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ)) (A B : Finset ι)
    (hAB : Disjoint A B) (hA : Even A.card) (hB : Even B.card) :
    correlation G ⟨J, 0, β⟩ (A ∪ B)
        - correlation G ⟨J, 0, β⟩ A * correlation G ⟨J, 0, β⟩ B
      ≤ ∑ A₁ ∈ A.powerset.filter (fun s => Odd s.card),
          ∑ B₁ ∈ B.powerset.filter (fun s => Odd s.card),
            correlation G ⟨J, 0, β⟩ (A₁ ∪ B₁)
              * correlation G ⟨J, 0, β⟩ ((A \ A₁) ∪ (B \ B₁)) := by
  have hcore := two_mul_correlation_union_sub_le G J β hf A B hAB hA hB
  have hSnn : 0 ≤ ∑ A₁ ∈ A.powerset.filter (fun s => Odd s.card),
      ∑ B₁ ∈ B.powerset.filter (fun s => Odd s.card),
        correlation G ⟨J, 0, β⟩ (A₁ ∪ B₁)
          * correlation G ⟨J, 0, β⟩ ((A \ A₁) ∪ (B \ B₁)) :=
    Finset.sum_nonneg fun A₁ _ => Finset.sum_nonneg fun B₁ _ =>
      mul_nonneg (gks_first G ⟨J, 0, β⟩ hf _) (gks_first G ⟨J, 0, β⟩ hf _)
  linarith

end Lebowitz

end IsingModel
