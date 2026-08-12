import IsingModel.Inequalities.SourcefreeConnectionEdgePivotal

/-!
# Clean (`∅`) leg of the per-edge switching identity (OZ Wall #2, Stage B2c)

This file formalises the **clean leg** (the `∅` / all-current ensemble leg) of the
per-edge switching identity underlying the *upper* (Ornstein–Zernike "Wall #2")
direction of the excess-current estimate for Glimm–Jaffe Theorem 17.5.1
(§17.5, p. 312; issue #4386, thread #4418).

Stage B1 decomposed the excess current per edge and Stage B2a
(`Current.edge_mul_doubledSourcefree_eq_defect`) extracted the `2βJ` factor: for
`0 < M e₀`, `(M e₀) · D(M) = 2βJ · D_{e₀}(M)`, where `D(M)` is the both-sourcefree
doubled summand (`Current.doubledSourcefreeSummand`) and `D_{e₀}(M)` is the doubled
*defect* summand (`Current.doubledDefectSummand`).  The clean leg computes the
`∅`-ensemble expectation of the edge occupation number:
`E^∅[M e₀] = (∑'_M (M e₀) D(M)) / (∑'_M D(M)) = 2βJ · ⟨σ_u σ_v⟩`,
where `e₀ = s(u, v)` (companion note `rc-oz-stageB2c-switching-identity.tex`,
Proposition "Clean leg", eq. (3.3)).

## Critical subtlety (load-bearing for correctness)

B2a is valid **only for `0 < M e₀`**: for `M e₀ = 0` the left side vanishes but
`D_{e₀}(M)` is generally nonzero.  Hence one must reindex the *numerator*
`∑'_M (M e₀) D(M)` — whose terms vanish off `{M | 1 ≤ M e₀}` — and never the defect
sum `∑'_M D_{e₀}(M)` over all `M`.  The reindexing bijection `M = M' + 1_{e₀}` is a
bijection **only** on `{M // 1 ≤ M e₀}`; it is packaged here as
`Current.edgeIncrementEquiv`.

## Main results

* `Current.edgeIncrementEquiv` — the bundled `Equiv`
  `{M // 1 ≤ M e₀} ≃ Current G Λ`, `M ↦ M − 1_{e₀}` (inverse `K ↦ K + 1_{e₀}`).
* `Current.tsum_edge_mul_doubledSourcefree_eq` — the core numerator identity
  `∑'_M (M e₀) D(M) = 2βJ · (weightSum {u,v} · weightSum ∅)`.
* `Current.doubledSourcefree_edgeExpectation_empty_eq` — the headline eq. (3.3):
  `(∑'_M (M e₀) D(M)) / (∑'_M D(M)) = 2βJ · ⟨σ_u σ_v⟩`.

The *pivotal* (reachable) leg (companion note §3.2, Steps P1/P2: the truncated
four-point ratio and the backbone bijection to the graph-pivotal probability) is a
separate research wall and is **not** treated here.

## References

* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality*
  (1992), Chapter 12.
* Aizenman, M. (1982) Geometric analysis of φ⁴ fields, Lemma 3.2, p. 7,
  eq. (3.5) (the switching lemma).
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5 Theorem 17.5.1 (p. 312).

(Issue #4386, thread #4418.)
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.unusedDecidableInType false in
/-- **Edge-increment `Equiv` (Stage B2c)**: for an edge `e₀`, the bijection
`{M : Current G Λ // 1 ≤ M e₀} ≃ Current G Λ` sending `M ↦ M − 1_{e₀}` (with
`1_{e₀} = Current.fromEdgeFinset G Λ {e₀}`), whose inverse is `K ↦ K + 1_{e₀}`.
This bundles the piecewise reindexing bijection appearing inside the Stage B2a
proof (`Current.edge_mul_doubledSourcefree_eq_defect`, step 3): decrementing one
copy of `e₀` is invertible precisely on currents with `1 ≤ M e₀` (so that the
truncated `Nat` subtraction at `e₀` is a genuine subtraction), and re-adding one
copy of `e₀` recovers the original current.  It is the reindexing device for the
numerator `∑'_M (M e₀) D(M)` of the clean leg of the per-edge switching identity
for Glimm–Jaffe Theorem 17.5.1 (issue #4386). -/
def Current.edgeIncrementEquiv (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) :
    {M : Current G Λ // 1 ≤ M e₀} ≃ Current G Λ where
  toFun x := (x : Current G Λ) - Current.fromEdgeFinset G Λ {e₀}
  invFun K := ⟨K + Current.fromEdgeFinset G Λ {e₀}, by
    simp only [Current.add_apply, Current.fromEdgeFinset, Finset.mem_singleton, ↓reduceIte]
    omega⟩
  left_inv := by
    rintro ⟨M, hM⟩
    apply Subtype.ext
    change (M - Current.fromEdgeFinset G Λ {e₀}) + Current.fromEdgeFinset G Λ {e₀} = M
    have hEle : Current.fromEdgeFinset G Λ {e₀} ≤ M := by
      intro e
      simp only [Current.fromEdgeFinset, Finset.mem_singleton]
      by_cases hee : e = e₀
      · subst hee; simpa using hM
      · simp only [if_neg hee]; omega
    exact Current.sub_add_cancel_of_le G Λ hEle
  right_inv := by
    intro K
    funext e
    simp only [Current.sub_apply, Current.add_apply]
    omega

set_option linter.unusedDecidableInType false in
/-- **Core numerator identity for the clean leg (Stage B2c)**: for non-negative
coupling `0 ≤ β J`, an edge `e₀ = s(u, v)`, the edge-weighted sum of the
both-sourcefree doubled summand equals `2βJ` times a product of partition masses,
`∑'_M (M e₀) · D(M) = 2 · (β J) · (weightSum {u,v} · weightSum ∅)`,
where `D(M) = Current.doubledSourcefreeSummand G Λ β J M`.

Proof.  The summand vanishes off `{M | 1 ≤ M e₀}` (factor `M e₀`), so restrict to
that subtype (`tsum_subtype_eq_of_support_subset`).  There Stage B2a
(`Current.edge_mul_doubledSourcefree_eq_defect`, valid since `0 < M e₀`) rewrites
each term as `2βJ · D_{e₀}(M)` with `D_{e₀}` the doubled defect summand
(`Current.doubledDefectSummand`).  Unfolding `D_{e₀}(M) = H(M − 1_{e₀})` — where
`H(K)` is the mixed `({u,v}, ∅)`-sourced doubled inner sum and `(e₀).toFinset =
{u,v}` by `Sym2.toFinset_mk_eq` — and reindexing `M = M' + 1_{e₀}` via
`Current.edgeIncrementEquiv` turns the numerator into `2βJ · ∑'_K H(K)`.  Finally
the Stage A product identity
`Current.weightSum_mul_weightSum_eq_tsum_doubled_subFinset` (with `A = {u,v}`,
`B = ∅`) identifies `∑'_K H(K) = weightSum {u,v} · weightSum ∅`.  (Aizenman 1982
§4 / FFS Chapter 12; Glimm–Jaffe Theorem 17.5.1, issue #4386.) -/
theorem Current.tsum_edge_mul_doubledSourcefree_eq
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (e₀ : (inducedGraph G Λ).edgeSet)
    (u v : ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(u, v)) :
    (∑' M : Current G Λ, (M e₀ : ℝ) * Current.doubledSourcefreeSummand G Λ β J M)
      = 2 * (β * J)
        * (Current.weightSum G Λ ({u, v} : Finset ↑Λ) β J
            * Current.weightSum G Λ ∅ β J) := by
  classical
  have htf : (e₀ : Sym2 ↑Λ).toFinset = ({u, v} : Finset ↑Λ) := by
    rw [hab, Sym2.toFinset_mk_eq]
  -- The mixed `({u,v}, ∅)`-sourced doubled inner summand.
  set H : Current G Λ → ℝ := fun K =>
    ∑ m ∈ (Current.subFinset G Λ K).filter
        (fun m => m.sources G Λ = ({u, v} : Finset ↑Λ) ∧ (K - m).sources G Λ = ∅),
      m.weight G Λ β J * (K - m).weight G Λ β J with hH
  -- Stage A product identity, folded through `H`.
  have hprod : Current.weightSum G Λ ({u, v} : Finset ↑Λ) β J
        * Current.weightSum G Λ ∅ β J = ∑' K : Current G Λ, H K := by
    simp only [hH]
    exact Current.weightSum_mul_weightSum_eq_tsum_doubled_subFinset G Λ {u, v} ∅ hβJ
  -- The defect summand is `H` reindexed by `M ↦ M − 1_{e₀}`.
  have hdefect : ∀ M : Current G Λ,
      Current.doubledDefectSummand G Λ e₀ β J M
        = H (M - Current.fromEdgeFinset G Λ {e₀}) := by
    intro M
    simp only [hH, Current.doubledDefectSummand, htf]
  -- The numerator is supported on `{M | 1 ≤ M e₀}`.
  have hsupp : Function.support
      (fun M : Current G Λ =>
        (M e₀ : ℝ) * Current.doubledSourcefreeSummand G Λ β J M)
      ⊆ {M : Current G Λ | 1 ≤ M e₀} := by
    intro M hM
    rw [Function.mem_support] at hM
    by_contra hcon
    simp only [Set.mem_setOf_eq, not_le, Nat.lt_one_iff] at hcon
    apply hM
    simp [hcon]
  calc (∑' M : Current G Λ, (M e₀ : ℝ) * Current.doubledSourcefreeSummand G Λ β J M)
      = ∑' x : {M : Current G Λ // 1 ≤ M e₀},
          ((x : Current G Λ) e₀ : ℝ)
            * Current.doubledSourcefreeSummand G Λ β J (x : Current G Λ) :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' x : {M : Current G Λ // 1 ≤ M e₀},
          2 * (β * J) * Current.doubledDefectSummand G Λ e₀ β J (x : Current G Λ) := by
        apply tsum_congr; intro x
        exact Current.edge_mul_doubledSourcefree_eq_defect G Λ β J (x : Current G Λ) e₀ x.2
    _ = 2 * (β * J) * ∑' x : {M : Current G Λ // 1 ≤ M e₀},
          Current.doubledDefectSummand G Λ e₀ β J (x : Current G Λ) := tsum_mul_left
    _ = 2 * (β * J) * ∑' x : {M : Current G Λ // 1 ≤ M e₀},
          H ((x : Current G Λ) - Current.fromEdgeFinset G Λ {e₀}) := by
        congr 1; apply tsum_congr; intro x; exact hdefect _
    _ = 2 * (β * J) * ∑' K : Current G Λ, H K := by
        congr 1; exact Equiv.tsum_eq (Current.edgeIncrementEquiv G Λ e₀) H
    _ = 2 * (β * J)
          * (Current.weightSum G Λ ({u, v} : Finset ↑Λ) β J
              * Current.weightSum G Λ ∅ β J) := by rw [hprod]

set_option linter.unusedDecidableInType false in
/-- **Clean-leg edge expectation (Stage B2c, eq. (3.3))**: for non-negative coupling
`0 ≤ β J` (zero field) and an edge `e₀ = s(u, v)`, the `∅`-ensemble expectation of
the edge occupation number is `2βJ` times the two-point function,
`(∑'_M (M e₀) D(M)) / (∑'_M D(M))
  = 2 · (β J) · ⟨σ_u σ_v⟩`,
where `D(M) = Current.doubledSourcefreeSummand G Λ β J M` and `⟨σ_u σ_v⟩ =
correlation (inducedGraph G Λ) ⟨J, 0, β⟩ {u, v}`.

Proof.  The numerator is `2βJ · (weightSum {u,v} · weightSum ∅)` by
`Current.tsum_edge_mul_doubledSourcefree_eq`; the denominator is `(weightSum ∅)²`
by U1 (`Current.weightSum_empty_sq_eq_tsum_doubled_sourcefree`); and `⟨σ_u σ_v⟩ =
weightSum {u,v} / weightSum ∅` by `correlation_inducedGraph_eq_weightSum_ratio`.
Since `weightSum ∅ > 0` (`Current.weightSum_empty_pos`), the resulting algebraic
identity closes by `field_simp`/`ring`.  This is the clean (`∅`) leg of the
per-edge switching identity underlying the Ornstein–Zernike Wall #2 upper bound for
Glimm–Jaffe Theorem 17.5.1 (§17.5, p. 312; companion note
`rc-oz-stageB2c-switching-identity.tex`, Proposition "Clean leg"; issue #4386,
thread #4418).  The pivotal (reachable) leg is deferred (research wall). -/
theorem Current.doubledSourcefree_edgeExpectation_empty_eq
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (e₀ : (inducedGraph G Λ).edgeSet)
    (u v : ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(u, v)) :
    (∑' M : Current G Λ, (M e₀ : ℝ) * Current.doubledSourcefreeSummand G Λ β J M)
        / (∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M)
      = 2 * (β * J)
        * correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ)
            ({u, v} : Finset ↑Λ) := by
  have hpos : 0 < Current.weightSum G Λ ∅ β J := Current.weightSum_empty_pos G Λ hβJ
  rw [Current.tsum_edge_mul_doubledSourcefree_eq G Λ hβJ e₀ u v hab,
    ← Current.weightSum_empty_sq_eq_tsum_doubled_sourcefree G Λ hβJ,
    correlation_inducedGraph_eq_weightSum_ratio G Λ hβJ {u, v}, pow_two]
  field_simp

end Ambient

end IsingModel
