import IsingModel.Inequalities.SourcefreeConnectionRatioDerivative
import Mathlib.Algebra.BigOperators.Field

/-!
# Per-edge decomposition of the excess current (OZ Wall #2, upper-bound Stage B1)

This file assembles **Stage B1** of the random-current build toward the
upper (Wall #2) direction of the Ornstein–Zernike excess-current estimate for
Glimm–Jaffe Theorem 17.5.1 (issue #4386, thread #4418).  The lower (sign)
direction — that conditioning on the connection event only *increases* the
`D`-normalised expected total current — is the sign-collapse brick
`Current.doubledSourcefree_excess_nonneg` (#4475).  The matching *upper* bound
`E^{x↔y}|M| − E^∅|M| ≤ C·d(x,y)` (FFS Ch. 12 / Aizenman 1982 Lemma 4.1) is
approached through a per-edge pivotal decomposition, of which **B1 is the honest
first brick**.

With induced edge set `E = (inducedGraph G Λ).edgeSet` (finite), the total
current size is `|M| = ∑_{e ∈ E} M e` (`Current.total`), so the total-weighted
current sum splits over edges:
\[
  \sum_{M} |M|\,D(M) = \sum_{e \in E} \sum_{M} (M\,e)\,D(M),
\]
and likewise over the connection-restricted (reachable) ensemble.  Dividing the
two numerators by their respective normalisations, the excess current decomposes
into a finite sum of per-edge contributions
\[
  E^{x↔y}|M| - E^{∅}|M|
    = \sum_{e \in E}\Big(\frac{\sum_{x↔y}(M\,e)D}{\sum_{x↔y}D}
        - \frac{\sum_M (M\,e)D}{\sum_M D}\Big).
\]
Each per-edge term will be identified in B2 (via the Aizenman switching lemma)
with `2βJ · ℙ^{x↔y}[e \text{ pivotal}]`, and the backbone-tail bound
`∑_e ℙ^{x↔y}[e \text{ pivotal}] ≤ K·d(x,y)` (deferred to B3, the genuine wall)
closes Wall #2.  This file supplies **only** the per-edge decomposition
identity; it does *not* address B2 (switching pivotal identity) or B3
(backbone-tail bound).

## Main results

* `Current.summable_edge_mul_doubledSourcefree` (B0) — per-edge summability of
  `M ↦ (M e)·D_β(M)`, dominated by the total-weighted summand (M2).
* `Current.tsum_total_mul_doubledSourcefree_eq_sum_edge` (B1 core, all currents) —
  `∑'_M |M|·D = ∑_e ∑'_M (M e)·D`.
* `Current.tsum_reachable_total_mul_doubledSourcefree_eq_sum_edge` (B1 core,
  reachable ensemble) — the same over `{M // Reachable x y}`.
* `Current.doubledSourcefree_excess_eq_sum_edge` (B1 corollary) — the excess
  current as a finite sum of per-edge ratio contributions.

## References

* Aizenman, M. (1982). Geometric analysis of φ⁴ fields, Lemma 4.1.
* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality*
  (1992), Chapter 12.
* Glimm–Jaffe, *Quantum Physics*, §17.5 Theorem 17.5.1 (p. 312).
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.unusedDecidableInType false in
/-- **B0 — per-edge summability of the current-weighted summand**: for `0 ≤ β`,
`0 ≤ J` and every induced edge `e`, the map `M ↦ (M e)·D_β(M)` is `Summable`.
Since `M e ≤ |M| = ∑_{e'} M e'` (a single non-negative summand, `Finset.single_le_sum`)
and `D_β(M) ≥ 0`, the term is dominated by `|M|·D_β(M)`, summable by M2
(`Current.summable_total_mul_doubledSourcefree`); `Summable.of_nonneg_of_le`
concludes. (FFS Chapter 12.) -/
theorem Current.summable_edge_mul_doubledSourcefree (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] {β J : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (e : (inducedGraph G Λ).edgeSet) :
    Summable (fun M : Current G Λ =>
      (M e : ℝ) * Current.doubledSourcefreeSummand G Λ β J M) := by
  have hβJ : 0 ≤ β * J := mul_nonneg hβ hJ
  refine Summable.of_nonneg_of_le ?_ ?_
    (Current.summable_total_mul_doubledSourcefree G Λ hβ hJ)
  · intro M
    exact mul_nonneg (Nat.cast_nonneg _)
      (Current.doubledSourcefreeSummand_nonneg G Λ hβJ M)
  · intro M
    have hnat : M e ≤ Current.total G Λ M :=
      Finset.single_le_sum (f := fun e' : (inducedGraph G Λ).edgeSet => M e')
        (fun i _ => Nat.zero_le _) (Finset.mem_univ e)
    have hle : (M e : ℝ) ≤ (Current.total G Λ M : ℝ) := by exact_mod_cast hnat
    exact mul_le_mul_of_nonneg_right hle
      (Current.doubledSourcefreeSummand_nonneg G Λ hβJ M)

set_option linter.unusedDecidableInType false in
/-- **B1 core (all currents) — per-edge decomposition of the total-weighted sum**:
for `0 ≤ β`, `0 ≤ J`,
`∑'_M |M|·D_β(M) = ∑_{e ∈ E} ∑'_M (M e)·D_β(M)`.
Unconditional (no division): `|M| = ∑_e M e` (`Current.total`) casts to
`∑_e (M e : ℝ)` (`Nat.cast_sum`); `Finset.sum_mul` distributes `D_β(M)` inside the
finite edge sum, and `Summable.tsum_finsetSum` (per-edge summability B0)
interchanges the finite edge sum with the `tsum`. (FFS Chapter 12 / Aizenman
1982 Lemma 4.1.) -/
theorem Current.tsum_total_mul_doubledSourcefree_eq_sum_edge (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] {β J : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    (∑' M : Current G Λ,
        (Current.total G Λ M : ℝ) * Current.doubledSourcefreeSummand G Λ β J M)
      = ∑ e : (inducedGraph G Λ).edgeSet,
          ∑' M : Current G Λ, (M e : ℝ) * Current.doubledSourcefreeSummand G Λ β J M := by
  have hcongr : (∑' M : Current G Λ,
        (Current.total G Λ M : ℝ) * Current.doubledSourcefreeSummand G Λ β J M)
      = ∑' M : Current G Λ, ∑ e : (inducedGraph G Λ).edgeSet,
          (M e : ℝ) * Current.doubledSourcefreeSummand G Λ β J M := by
    refine tsum_congr (fun M => ?_)
    have hcast : (Current.total G Λ M : ℝ)
        = ∑ e : (inducedGraph G Λ).edgeSet, (M e : ℝ) := by
      simp only [Current.total, Nat.cast_sum]
    rw [hcast, Finset.sum_mul]
  rw [hcongr,
    Summable.tsum_finsetSum
      (fun e _ => Current.summable_edge_mul_doubledSourcefree G Λ hβ hJ e)]

set_option linter.unusedDecidableInType false in
/-- **B1 core (reachable ensemble) — per-edge decomposition of the connected
total-weighted sum**: for `0 ≤ β`, `0 ≤ J` and `x, y ∈ Λ`, over the reachability
subtype `{M // (M.toSimpleGraph).Reachable x y}`,
`∑'_{x↔y} |M|·D_β(M) = ∑_{e ∈ E} ∑'_{x↔y} (M e)·D_β(M)`.
Same proof shape as the all-currents version, with the per-edge summability B0
transported to the subtype via `Summable.comp_injective` (injectivity of
`Subtype.val`). (FFS Chapter 12 / Aizenman 1982 Lemma 4.1.) -/
theorem Current.tsum_reachable_total_mul_doubledSourcefree_eq_sum_edge (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (x y : ↑Λ) {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
        (Current.total G Λ (M : Current G Λ) : ℝ)
          * Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ))
      = ∑ e : (inducedGraph G Λ).edgeSet,
          ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
            ((M : Current G Λ) e : ℝ)
              * Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ) := by
  have hcongr : (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
        (Current.total G Λ (M : Current G Λ) : ℝ)
          * Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ))
      = ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
          ∑ e : (inducedGraph G Λ).edgeSet,
            ((M : Current G Λ) e : ℝ)
              * Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ) := by
    refine tsum_congr (fun M => ?_)
    have hcast : (Current.total G Λ (M : Current G Λ) : ℝ)
        = ∑ e : (inducedGraph G Λ).edgeSet, ((M : Current G Λ) e : ℝ) := by
      simp only [Current.total, Nat.cast_sum]
    rw [hcast, Finset.sum_mul]
  have hsum : ∀ e ∈ (Finset.univ : Finset (inducedGraph G Λ).edgeSet),
      Summable (fun M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y} =>
        ((M : Current G Λ) e : ℝ)
          * Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ)) :=
    fun e _ => (Current.summable_edge_mul_doubledSourcefree G Λ hβ hJ e).comp_injective
      Subtype.val_injective
  rw [hcongr, Summable.tsum_finsetSum hsum]

set_option linter.unusedDecidableInType false in
/-- **B1 corollary — the excess current as a per-edge sum**: for `0 ≤ β`,
`0 ≤ J` and `x, y ∈ Λ`, the excess of the `D`-normalised expected total current
decomposes into a finite sum of per-edge ratio contributions,
\[
  \frac{\sum_{x↔y}|M|D}{\sum_{x↔y}D} - \frac{\sum_M |M|D}{\sum_M D}
    = \sum_{e ∈ E}\Big(\frac{\sum_{x↔y}(M\,e)D}{\sum_{x↔y}D}
        - \frac{\sum_M (M\,e)D}{\sum_M D}\Big).
\]
Purely algebraic: rewrite both numerators by the B1 core decompositions, then
`Finset.sum_div` distributes each denominator through the edge sum and
`Finset.sum_sub_distrib` merges the two edge sums into one.  No positivity of the
denominators is needed (division is total).  Combined with the sign-collapse
brick `Current.doubledSourcefree_excess_nonneg` (#4475), this expresses the
non-negative excess `E^{x↔y}|M| − E^∅|M|` as a sum of per-edge ratio-difference
contributions; the identification of each per-edge term with
`2βJ · ℙ^{x↔y}[e \text{ pivotal}]` (B2, switching lemma) and the backbone-tail
bound (B3, the genuine Wall #2 estimate) are deferred to later bricks.
(FFS Chapter 12 / Aizenman 1982 Lemma 4.1 / GJ §17.5 Theorem 17.5.1, p. 312.) -/
theorem Current.doubledSourcefree_excess_eq_sum_edge (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] (x y : ↑Λ) {β J : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
          (Current.total G Λ (M : Current G Λ) : ℝ)
            * Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ))
        / ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
            Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ)
      - (∑' M : Current G Λ,
            (Current.total G Λ M : ℝ) * Current.doubledSourcefreeSummand G Λ β J M)
          / ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M
      = ∑ e : (inducedGraph G Λ).edgeSet,
          ((∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
                ((M : Current G Λ) e : ℝ)
                  * Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ))
              / ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
                  Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ)
            - (∑' M : Current G Λ,
                  (M e : ℝ) * Current.doubledSourcefreeSummand G Λ β J M)
                / ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M) := by
  rw [Current.tsum_reachable_total_mul_doubledSourcefree_eq_sum_edge G Λ x y hβ hJ,
    Current.tsum_total_mul_doubledSourcefree_eq_sum_edge G Λ hβ hJ,
    Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]

end Ambient

end IsingModel
