import IsingModel.ClusterExpansion.UrsellTreeBound
import IsingModel.ClusterExpansion.Penrose.SpanningTreeSummable

/-!
# Absolute convergence of the Mayer expansion (GJ §18.4-18.5)

The cluster-expansion convergence (Issue #3954, milestone M2) is completed here:
the Mayer series `∑ₙ mayerExpansionTerm G n t` converges absolutely in the
high-temperature regime, by majorising each term with the summable spanning-tree
majorant of `SpanningTreeSummable.lean`.

The chain is:
* the Ursell coefficient is bounded uniformly in the polymer sequence,
  `|ϕ^T(ω)| ≤ numSpanningTrees (⊤ : SimpleGraph (Fin n)) / n!`
  (`ursellCoefficient_abs_le_numSpanningTrees_top_div_factorial`);
* the total activity over `n`-tuples factorises,
  `∑_{ω} |z(t,ω)| = (∑_{P} |t|^{|P|})^n`
  (`Finset.sum_prod_piFinset`), so that
  `|mayerExpansionTerm G n t| ≤ numSpanningTrees (⊤ Fin n) / n! · A^n`
  with `A = ∑_{P ∈ allPolymers G} |t|^{|P|}`;
* this is exactly the `SpanningTreeSummable` majorant at `R = A`, so
  `Summable (fun n => mayerExpansionTerm G n t)` whenever `e·A < 1`.

The remaining M2 steps (`log Ξ = ∑ₙ mayerExpansionTerm` in the
Kotecký–Preiss regime, and the high-temperature Ising specialisation
`t = tanh(βJ)`) build on this absolute convergence.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4 (p. 332) – §18.5 (p. 335).
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §5.7.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Absolute cluster-sequence activity as a product**:
`|z(t,ω)| = ∏ᵢ |t|^{|ω i|}`, the absolute value distributing over the product. -/
theorem clusterSeqActivity_abs {n : ℕ} (t : ℝ) (ω : Fin n → Finset (Sym2 ι)) :
    |clusterSeqActivity t ω| = ∏ i : Fin n, |t| ^ (ω i).card := by
  rw [clusterSeqActivity, Finset.abs_prod]
  exact Finset.prod_congr rfl (fun i _ => abs_pow t (ω i).card)

/-- **Total absolute activity over `n`-tuples factorises**:
`∑_{ω ∈ piFinset (allPolymers G)} |z(t,ω)| = (∑_{P ∈ allPolymers G} |t|^{|P|})^n`,
by the product–sum expansion over a constant `piFinset` (`Finset.sum_prod_piFinset`). -/
theorem sum_clusterSeqActivity_abs_piFinset
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (t : ℝ) :
    (∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
        |clusterSeqActivity t ω|)
      = (∑ P ∈ allPolymers G, |t| ^ P.card) ^ n := by
  calc
    (∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
        |clusterSeqActivity t ω|)
        = ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
            ∏ i : Fin n, |t| ^ (ω i).card := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          exact clusterSeqActivity_abs t ω
    _ = ∏ _i : Fin n, ∑ P ∈ allPolymers G, |t| ^ P.card :=
          Finset.sum_prod_piFinset (allPolymers G) (fun (_ : Fin n) P => |t| ^ P.card)
    _ = (∑ P ∈ allPolymers G, |t| ^ P.card) ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Mayer-term bound by the spanning-tree majorant**:
`|mayerExpansionTerm G n t| ≤ numSpanningTrees (⊤ Fin n) / n! · (∑_{P} |t|^{|P|})^n`,
combining the uniform Ursell bound with the factorised total activity. -/
theorem mayerExpansionTerm_abs_le_tree_activity_pow
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (t : ℝ) :
    |mayerExpansionTerm G n t| ≤
      ((Penrose.numSpanningTrees (⊤ : SimpleGraph (Fin n)) : ℝ) / (n.factorial : ℝ)) *
        (∑ P ∈ allPolymers G, |t| ^ P.card) ^ n := by
  set C : ℝ := (Penrose.numSpanningTrees (⊤ : SimpleGraph (Fin n)) : ℝ) / (n.factorial : ℝ) with hC
  refine (mayerExpansionTerm_abs_le G n t).trans ?_
  have hsum_le :
      (∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
          |ursellCoefficient ω| * |clusterSeqActivity t ω|)
        ≤ ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
            C * |clusterSeqActivity t ω| := by
    refine Finset.sum_le_sum ?_
    intro ω _
    exact mul_le_mul_of_nonneg_right
      (by simpa [hC] using
        ursellCoefficient_abs_le_numSpanningTrees_top_div_factorial (ω := ω))
      (abs_nonneg _)
  refine hsum_le.trans_eq ?_
  rw [← Finset.mul_sum, sum_clusterSeqActivity_abs_piFinset]

/-- **Absolute convergence of the Mayer expansion (high temperature)**:
if `e · (∑_{P ∈ allPolymers G} |t|^{|P|}) < 1`, then
`Summable (fun n => mayerExpansionTerm G n t)`.  The polymer-activity sum `A`
plays the role of the radius parameter `R` of the spanning-tree majorant; the
condition is `A < 1/e`.  This is the cluster-expansion absolute convergence
`∑ₙ mayerExpansionTerm` for general interacting polymers. -/
theorem summable_mayerExpansionTerm_of_exp_one_mul_activity_lt_one
    (G : SimpleGraph ι) [Fintype G.edgeSet] {t : ℝ}
    (ht : Real.exp 1 * (∑ P ∈ allPolymers G, |t| ^ P.card) < 1) :
    Summable (fun n : ℕ => mayerExpansionTerm G n t) := by
  set A : ℝ := ∑ P ∈ allPolymers G, |t| ^ P.card with hA
  have hA_nonneg : 0 ≤ A := by
    rw [hA]; exact Finset.sum_nonneg (fun P _ => pow_nonneg (abs_nonneg t) P.card)
  have hmajor : Summable (fun n : ℕ =>
      ((Penrose.numSpanningTrees (⊤ : SimpleGraph (Fin n)) : ℝ) / (n.factorial : ℝ)) * A ^ n) :=
    Penrose.summable_completeGraph_numSpanningTrees_div_factorial_mul_pow A
      (by rw [abs_of_nonneg hA_nonneg]; exact ht)
  refine hmajor.of_norm_bounded ?_
  intro n
  rw [Real.norm_eq_abs]
  simpa [hA] using mayerExpansionTerm_abs_le_tree_activity_pow G n t

omit [Fintype ι] in
/-- **Polymer-activity sum bound for `|t| ≤ 1`**:
`∑_{P ∈ allPolymers G} |t|^{|P|} ≤ |allPolymers G| · |t|`, since every polymer has
at least one edge (`|P| ≥ 1`) and `|t|^{|P|} ≤ |t|` when `|t| ≤ 1`. -/
theorem activity_sum_le_card_mul_abs
    (G : SimpleGraph ι) [Fintype G.edgeSet] {t : ℝ} (ht : |t| ≤ 1) :
    (∑ P ∈ allPolymers G, |t| ^ P.card) ≤ (allPolymers G).card * |t| := by
  calc (∑ P ∈ allPolymers G, |t| ^ P.card)
      ≤ ∑ _P ∈ allPolymers G, |t| := by
        refine Finset.sum_le_sum (fun P hP => ?_)
        have hPcard : 1 ≤ P.card :=
          Finset.one_le_card.mpr (mem_allPolymers.mp hP).nonempty
        calc |t| ^ P.card ≤ |t| ^ 1 := pow_le_pow_of_le_one (abs_nonneg t) ht hPcard
          _ = |t| := pow_one _
    _ = (allPolymers G).card * |t| := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Absolute convergence of the Mayer expansion (usable high-temperature form)**:
if `|t| ≤ 1` and `e · |allPolymers G| · |t| < 1`, then
`Summable (fun n => mayerExpansionTerm G n t)`.  A clean sufficient condition for
the cluster expansion to converge: it suffices that the activity `|t|` be smaller
than `1 / (e · |allPolymers G|)`. -/
theorem summable_mayerExpansionTerm_of_card_mul_lt
    (G : SimpleGraph ι) [Fintype G.edgeSet] {t : ℝ} (ht1 : |t| ≤ 1)
    (ht : Real.exp 1 * ((allPolymers G).card * |t|) < 1) :
    Summable (fun n : ℕ => mayerExpansionTerm G n t) := by
  refine summable_mayerExpansionTerm_of_exp_one_mul_activity_lt_one G ?_
  refine lt_of_le_of_lt ?_ ht
  exact mul_le_mul_of_nonneg_left (activity_sum_le_card_mul_abs G ht1) (Real.exp_pos 1).le

end IsingModel
