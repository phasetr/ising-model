import IsingModel.ClusterExpansion.FieldPolymerActivity
import IsingModel.ClusterExpansion.UrsellTreeBound
import IsingModel.ClusterExpansion.Penrose.SpanningTreeSummable

/-!
# Field-dependent Mayer term and its dominated summability (GJ §17.6.1)

Brick 3 of the on-book programme toward Glimm–Jaffe (GJ) Theorem 17.6.1
(`∂/∂h` infinite-volume differentiability / `h`-analyticity of the two-point
function in the high-temperature window).  Brick 2a
(`allSubgraphs_sum_eq_vdConnectedPolymerFamilies_sum`,
`Families/FieldConnectedPolymers.lean`) exhibited the finite-volume partition
function as a hard-core gas of the field-dependent *connected* polymers with
weight `w_{a,b}(P) = tanh(a)^|P|·tanh(b)^{#odd(P)}`; brick 2b
(`FieldPolymerActivity.lean`) supplied the volume-uniform activity bounds whose
combinatorial heart is the term-wise weight reduction
`|w_{a,b}(P)| ≤ |tanh a|^|P|` (`abs_fieldPolymerWeight_le`).

This brick supplies the **convergence input** of the field Mayer expansion:
the field cluster-sequence activity `fieldClusterSeqActivity` (the multiplicative
carry of the field weight, mirroring `clusterSeqActivity`), the field Mayer term
`fieldMayerExpansionTerm` (the weight-agnostic Ursell coefficient
`ursellCoefficient` reused *verbatim*, summed over the connected species
`allConnectedPolymers`), and its **term-by-term dominated summability** obtained
by comparison against the already-established `h = 0` spanning-tree Mayer
majorant at the specialised activity `t = |tanh a|`.

No new hard analysis: brick 3 is pure comparison.  The domination
`|fieldClusterSeqActivity a b ω| ≤ clusterSeqActivity |tanh a| ω`
(`abs_fieldClusterSeqActivity_le`) collapses the field convergence onto the
`h = 0` convergence, and the species- and weight-agnostic spanning-tree majorant
`Penrose.summable_completeGraph_numSpanningTrees_div_factorial_mul_pow` (used
verbatim for the even species in `MayerCore/UrsellMajorant.lean`) closes
summability under the same high-temperature smallness `e·A < 1` with
`A = ∑_{P ∈ allConnectedPolymers G} |tanh a|^|P|`.

Real `h` only.  Complex `h` (where `|tanh b|` need not be `≤ 1`, requiring the
`M²`-domination `|w_ℂ(P)| ≤ (M²|tanh a|)^|P|` via `#odd(P) ≤ 2|P|`) is deferred
to a later non-vanishing brick.  Regression at `b = 0`: `tanh 0 = 0`, so
`fieldPolymerWeight a 0 P = tanh a^|P|·0^{#odd(P)}` collapses to `tanh a^|P|` on
even polymers and vanishes otherwise, matching the `h = 0` even restriction.

## References

* Friedli–Velenik §5.3, Proposition 5.3, gives the formal Mayer/Ursell identity,
  and §5.4, Theorem 5.4, p. 224, gives convergence.
* Friedli–Velenik Exercise 5.8, p. 238, with its Appendix C solution, p. 531,
  gives the exact real-field weight. The dominated term comparison here is a
  project extension.
* Kotecký–Preiss Theorem 1 supplies only the abstract convergence criterion.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Field cluster-sequence activity** `∏ᵢ w_{a,b}(ω i)`.  For a cluster
sequence `ω : Fin n → Finset (Sym2 ι)` the field activity factor is the
multiplicative product of the field polymer weights `fieldPolymerWeight a b`,
the field mirror of `clusterSeqActivity t ω = ∏ᵢ t^{|ω i|}`: the field weight
is carried multiplicatively in place of the monomial `t^{|ω i|}`. -/
noncomputable def fieldClusterSeqActivity (a b : ℝ) {n : ℕ}
    (ω : Fin n → Finset (Sym2 ι)) : ℝ :=
  ∏ i : Fin n, fieldPolymerWeight a b (ω i)

/-- **Field Mayer expansion `n`-th term** `∑_ω ϕ^T(ω)·∏ᵢ w_{a,b}(ω i)`.  The
weight-agnostic Ursell coefficient `ursellCoefficient` (which grades by the
sequence of supports only, not by any activity/weight) is reused *verbatim*; the
reference universe is the connected species `allConnectedPolymers G` (brick 2a,
the parity restriction of the even species `allPolymers G` dropped), and the
activity factor is `fieldClusterSeqActivity`.  Field mirror of
`mayerExpansionTerm G n t`; the `1/n!` is already absorbed into
`ursellCoefficient`. -/
noncomputable def fieldMayerExpansionTerm (G : SimpleGraph ι) [Fintype G.edgeSet]
    (n : ℕ) (a b : ℝ) : ℝ :=
  ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G),
    ursellCoefficient ω * fieldClusterSeqActivity a b ω

/-- **Term-by-term domination** of the field activity by the `h = 0` activity at
`t = |tanh a|`: `|fieldClusterSeqActivity a b ω| ≤ clusterSeqActivity |tanh a| ω`
`= ∏ᵢ |tanh a|^{|ω i|}`.  The absolute value distributes over the product
(`Finset.abs_prod`) and factorwise `|w_{a,b}(ω i)| ≤ |tanh a|^{|ω i|}`
(`abs_fieldPolymerWeight_le`, valid for all real `b` since `|tanh b| < 1`);
`Finset.prod_le_prod` closes it (each factor non-negative). -/
theorem abs_fieldClusterSeqActivity_le (a b : ℝ) {n : ℕ}
    (ω : Fin n → Finset (Sym2 ι)) :
    |fieldClusterSeqActivity a b ω| ≤ clusterSeqActivity |Real.tanh a| ω := by
  rw [fieldClusterSeqActivity, clusterSeqActivity, Finset.abs_prod]
  exact Finset.prod_le_prod (fun i _ => abs_nonneg _)
    (fun i _ => abs_fieldPolymerWeight_le a b (ω i))

/-- **Total activity over connected `n`-tuples factorises**:
`∑_{ω ∈ piFinset (allConnectedPolymers G)} clusterSeqActivity t ω =
(∑_{P ∈ allConnectedPolymers G} t^{|P|})^n`, by the product–sum expansion over a
constant `piFinset` (`Finset.sum_prod_piFinset`).  Connected-species mirror of
`sum_clusterSeqActivity_abs_piFinset`. -/
theorem sum_clusterSeqActivity_piFinset_connected
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (t : ℝ) :
    (∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G),
        clusterSeqActivity t ω)
      = (∑ P ∈ allConnectedPolymers G, t ^ P.card) ^ n := by
  calc
    (∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G),
        clusterSeqActivity t ω)
        = ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G),
            ∏ i : Fin n, t ^ (ω i).card := by
          refine Finset.sum_congr rfl (fun ω _ => ?_)
          rw [clusterSeqActivity]
    _ = ∏ _i : Fin n, ∑ P ∈ allConnectedPolymers G, t ^ P.card :=
          Finset.sum_prod_piFinset (allConnectedPolymers G)
            (fun (_ : Fin n) P => t ^ P.card)
    _ = (∑ P ∈ allConnectedPolymers G, t ^ P.card) ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Field Mayer-term absolute bound** (triangle inequality):
`|fieldMayerExpansionTerm G n a b| ≤ ∑_ω |ϕ^T(ω)|·|fieldClusterSeqActivity a b ω|`.
Field mirror of `mayerExpansionTerm_abs_le`. -/
theorem fieldMayerExpansionTerm_abs_le (G : SimpleGraph ι) [Fintype G.edgeSet]
    (n : ℕ) (a b : ℝ) :
    |fieldMayerExpansionTerm G n a b| ≤
      ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G),
        |ursellCoefficient ω| * |fieldClusterSeqActivity a b ω| := by
  unfold fieldMayerExpansionTerm
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun ω _ => abs_mul _ _)

/-- **Field Mayer-term bound by the spanning-tree majorant**:
`|fieldMayerExpansionTerm G n a b| ≤ numSpanningTrees (⊤ Fin n) / n! ·
(∑_{P ∈ allConnectedPolymers G} |tanh a|^{|P|})^n`.  Combines the uniform Ursell
bound `ursellCoefficient_abs_le_numSpanningTrees_top_div_factorial` with the
term-by-term domination `abs_fieldClusterSeqActivity_le` and the factorised total
activity `sum_clusterSeqActivity_piFinset_connected`.  Field/connected-species
mirror of `mayerExpansionTerm_abs_le_tree_activity_pow`. -/
theorem fieldMayerExpansionTerm_abs_le_tree_activity_pow
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (a b : ℝ) :
    |fieldMayerExpansionTerm G n a b| ≤
      ((Penrose.numSpanningTrees (⊤ : SimpleGraph (Fin n)) : ℝ) /
          (n.factorial : ℝ)) *
        (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ n := by
  set C : ℝ := (Penrose.numSpanningTrees (⊤ : SimpleGraph (Fin n)) : ℝ) /
    (n.factorial : ℝ) with hC
  refine (fieldMayerExpansionTerm_abs_le G n a b).trans ?_
  have hsum_le :
      (∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G),
          |ursellCoefficient ω| * |fieldClusterSeqActivity a b ω|)
        ≤ ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G),
            C * clusterSeqActivity |Real.tanh a| ω := by
    refine Finset.sum_le_sum (fun ω _ => ?_)
    have hcsa : 0 ≤ clusterSeqActivity |Real.tanh a| ω := by
      rw [clusterSeqActivity]
      exact Finset.prod_nonneg (fun i _ => pow_nonneg (abs_nonneg _) _)
    calc |ursellCoefficient ω| * |fieldClusterSeqActivity a b ω|
        ≤ |ursellCoefficient ω| * clusterSeqActivity |Real.tanh a| ω :=
          mul_le_mul_of_nonneg_left (abs_fieldClusterSeqActivity_le a b ω)
            (abs_nonneg _)
      _ ≤ C * clusterSeqActivity |Real.tanh a| ω :=
          mul_le_mul_of_nonneg_right
            (by simpa [hC] using
              ursellCoefficient_abs_le_numSpanningTrees_top_div_factorial (ω := ω))
            hcsa
  refine hsum_le.trans_eq ?_
  rw [← Finset.mul_sum, sum_clusterSeqActivity_piFinset_connected]

/-- **Dominated summability of the field Mayer series (high temperature)**:
if `e · (∑_{P ∈ allConnectedPolymers G} |tanh a|^{|P|}) < 1`, then
`Summable (fun n => fieldMayerExpansionTerm G n a b)` for every real `b`.  The
field convergence is collapsed onto the `h = 0` convergence at `t = |tanh a|`:
each field Mayer term is dominated by the spanning-tree majorant
`Penrose.summable_completeGraph_numSpanningTrees_div_factorial_mul_pow` at
`R = A = ∑_{P ∈ allConnectedPolymers G} |tanh a|^{|P|}`, which is summable under
`e·A < 1` — the connected-species analogue of
`summable_mayerExpansionTerm_of_exp_one_mul_activity_lt_one`.  No new analysis:
pure comparison via the brick 2b weight bound. -/
theorem summable_fieldMayerExpansionTerm (G : SimpleGraph ι) [Fintype G.edgeSet]
    {a b : ℝ}
    (hact : Real.exp 1 *
      (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) < 1) :
    Summable (fun n : ℕ => fieldMayerExpansionTerm G n a b) := by
  set A : ℝ := ∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card with hA
  have hA_nonneg : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg (fun P _ => pow_nonneg (abs_nonneg _) P.card)
  have hmajor : Summable (fun n : ℕ =>
      ((Penrose.numSpanningTrees (⊤ : SimpleGraph (Fin n)) : ℝ) /
        (n.factorial : ℝ)) * A ^ n) :=
    Penrose.summable_completeGraph_numSpanningTrees_div_factorial_mul_pow A
      (by rw [abs_of_nonneg hA_nonneg]; exact hact)
  refine hmajor.of_norm_bounded ?_
  intro n
  rw [Real.norm_eq_abs]
  simpa [hA] using fieldMayerExpansionTerm_abs_le_tree_activity_pow G n a b

end IsingModel
