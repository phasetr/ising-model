import IsingModel.Inequalities.SourcefreeConnectionRatioDerivative
import IsingModel.RandomCurrent.Peeling
import Mathlib.Algebra.BigOperators.Field

/-!
# Doubled defect-summand identity (OZ Wall #2 upper bound, Stage B2a)

This file assembles **Stage B2a** of the random-current build toward the *upper*
(Ornstein–Zernike Wall #2) direction of the excess-current estimate for
Glimm–Jaffe Theorem 17.5.1 (issue #4386, thread #4418).  The excess current was
decomposed per edge in Stage B1
(`Current.doubledSourcefree_excess_eq_sum_edge`, PR #4476): each per-edge term is
`E^{x↔y}[M e] − E^∅[M e]`, and the FFS Ch. 12 / Aizenman 1982 programme rewrites
it as `2βJ · ℙ^{x↔y}[e pivotal]`.  Stage B2a extracts the **`2βJ` factor and the
defect structure** — the honest algebraic first step, before any pivotal graph
event (B2b) or new switching identity (B2c) is introduced.

With induced edge set `E = (inducedGraph G Λ).edgeSet` (finite), the
both-sourcefree doubled inner summand is
`D(M) = ∑_{m ≤ M, ∂m = ∅, ∂(M − m) = ∅} w(m) w(M − m)`
(`Current.doubledSourcefreeSummand`).  For an edge `e₀`, the **doubled defect
summand** `D_{e₀}(M)` is the analogous inner sum over the *decremented* total
`M − 1_{e₀}` (with `1_{e₀} = Current.fromEdgeFinset G Λ {e₀}`) whose distinguished
piece carries the two endpoints of `e₀` as its defect source pattern:
`D_{e₀}(M) = ∑_{m ≤ M − 1_{e₀}, ∂m = {endpoints e₀}, ∂((M − 1_{e₀}) − m) = ∅}
             w(m) w((M − 1_{e₀}) − m)`.

## Main results

* `Current.doubledDefectSummand` — the doubled defect summand `D_{e₀}(M)`.
* `Current.edge_mul_doubledSourcefree_eq_defect` — for `0 < M e₀`,
  `(M e₀) · D(M) = 2 · (β J) · D_{e₀}(M)`.  The proof combines the switching
  involution `m ↦ M − m` (factor `2`), the weight-peeling identity
  `(m e₀) w(m) = βJ w(m − 1_{e₀})` (`Current.weight_pred_edge`), and the
  source-parity shift `∂(m − 1_{e₀}) = symmDiff (∂m) (endpoints e₀)`
  (`Current.sources_sub_edge_symmDiff`).

## References

* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality*
  (1992), Chapter 12.
* Aizenman, M. (1982) Geometric analysis of φ⁴ fields, Lemma 4.1.
* Glimm–Jaffe, *Quantum Physics*, §17.5 Theorem 17.5.1 (p. 312).

(Issue #4386, thread #4418.)
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.unusedDecidableInType false in
/-- **Doubled defect summand `D_{e₀}(M)`**: for a doubled current `M` and an edge
`e₀`, the finite inner sum over splittings of the decremented total
`M − 1_{e₀}` (with `1_{e₀} = Current.fromEdgeFinset G Λ {e₀}`) whose distinguished
piece `m` carries the two endpoints of `e₀` as its defect source pattern and whose
complement is sourcefree,
`D_{e₀}(M) = ∑_{m ≤ M − 1_{e₀}, ∂m = {endpoints e₀}, ∂((M − 1_{e₀}) − m) = ∅}
             w(m) w((M − 1_{e₀}) − m)`.
This is the reindexed image (under `m ↦ m − 1_{e₀}`) of the edge-weighted
sourcefree summand appearing in the Wall #2 upper bound of Glimm–Jaffe
Theorem 17.5.1 (issue #4386). -/
noncomputable def Current.doubledDefectSummand
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) (β J : ℝ) (M : Current G Λ) : ℝ :=
  ∑ m ∈ (Current.subFinset G Λ (M - Current.fromEdgeFinset G Λ {e₀})).filter
      (fun m => m.sources G Λ = (e₀ : Sym2 ↑Λ).toFinset ∧
        ((M - Current.fromEdgeFinset G Λ {e₀}) - m).sources G Λ = ∅),
    m.weight G Λ β J *
      ((M - Current.fromEdgeFinset G Λ {e₀}) - m).weight G Λ β J

set_option linter.unusedDecidableInType false in
/-- **Edge-multiplied sourcefree summand as a doubled defect summand (Stage B2a)**:
for a doubled current `M` and an edge `e₀` with `0 < M e₀`,
`(M e₀) · D(M) = 2 · (β J) · D_{e₀}(M)`, where `D(M)` is the both-sourcefree
doubled summand (`Current.doubledSourcefreeSummand`) and `D_{e₀}(M)` is the doubled
defect summand (`Current.doubledDefectSummand`).

Proof.  Writing `M e₀ = m e₀ + (M − m) e₀` on each splitting, the sum splits into
two halves; the switching involution `m ↦ M − m` (weight-preserving, `sources`
symmetric) equates them, producing the factor `2` and reducing to
`2 · ∑_{∂m = ∅, ∂(M − m) = ∅} (m e₀) w(m) w(M − m)`.  The zero terms `m e₀ = 0`
drop, and on `0 < m e₀` the weight-peeling identity `Current.weight_pred_edge`
gives `(m e₀) w(m) = βJ · w(m − 1_{e₀})`.  Reindexing `m' = m − 1_{e₀}` (a
bijection onto the defect filter, with `∂m' = {endpoints e₀}` by
`Current.sources_sub_edge_symmDiff` and `(M − 1_{e₀}) − m' = M − m`) identifies the
remaining sum with `βJ · D_{e₀}(M)`.  This is the `2βJ`-factor / defect-structure
extraction step of the FFS Ch. 12 / Aizenman 1982 upper bound for Glimm–Jaffe
Theorem 17.5.1 (issue #4386; the pivotal graph event and the new switching
identity are deferred bricks B2b/B2c). -/
theorem Current.edge_mul_doubledSourcefree_eq_defect
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (M : Current G Λ) (e₀ : (inducedGraph G Λ).edgeSet)
    (he : 0 < M e₀) :
    (M e₀ : ℝ) * Current.doubledSourcefreeSummand G Λ β J M
      = 2 * (β * J) * Current.doubledDefectSummand G Λ e₀ β J M := by
  classical
  simp only [Current.doubledSourcefreeSummand, Current.doubledDefectSummand]
  -- Split `M e₀ · D(M)` into the `m e₀` half and the `(M − m) e₀` half.
  have step1 : (M e₀ : ℝ) * ∑ m ∈ (Current.subFinset G Λ M).filter
        (fun m => m.sources G Λ = ∅ ∧ (M - m).sources G Λ = ∅),
        m.weight G Λ β J * (M - m).weight G Λ β J
      = (∑ m ∈ (Current.subFinset G Λ M).filter
          (fun m => m.sources G Λ = ∅ ∧ (M - m).sources G Λ = ∅),
          (m e₀ : ℝ) * (m.weight G Λ β J * (M - m).weight G Λ β J))
        + (∑ m ∈ (Current.subFinset G Λ M).filter
          (fun m => m.sources G Λ = ∅ ∧ (M - m).sources G Λ = ∅),
          ((M - m) e₀ : ℝ) * (m.weight G Λ β J * (M - m).weight G Λ β J)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [Finset.mem_filter, Current.mem_subFinset_iff] at hm
    obtain ⟨hmle, -⟩ := hm
    have hle : m e₀ ≤ M e₀ := hmle e₀
    have hnat : m e₀ + (M - m) e₀ = M e₀ := by
      rw [Current.sub_apply]; omega
    have hcast : (M e₀ : ℝ) = (m e₀ : ℝ) + ((M - m) e₀ : ℝ) := by
      rw [← hnat]; push_cast; ring
    rw [hcast]; ring
  -- The switching involution `m ↦ M − m` equates the two halves.
  have step2 : (∑ m ∈ (Current.subFinset G Λ M).filter
        (fun m => m.sources G Λ = ∅ ∧ (M - m).sources G Λ = ∅),
        ((M - m) e₀ : ℝ) * (m.weight G Λ β J * (M - m).weight G Λ β J))
      = ∑ m ∈ (Current.subFinset G Λ M).filter
        (fun m => m.sources G Λ = ∅ ∧ (M - m).sources G Λ = ∅),
        (m e₀ : ℝ) * (m.weight G Λ β J * (M - m).weight G Λ β J) := by
    refine Finset.sum_nbij' (fun m => M - m) (fun m => M - m) ?_ ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_filter, Current.mem_subFinset_iff] at hm ⊢
      obtain ⟨hmle, hm0, hmM0⟩ := hm
      refine ⟨Current.sub_le_self G Λ M m, hmM0, ?_⟩
      rw [Current.sub_sub_self_of_le G Λ hmle]; exact hm0
    · intro m hm
      simp only [Finset.mem_filter, Current.mem_subFinset_iff] at hm ⊢
      obtain ⟨hmle, hm0, hmM0⟩ := hm
      refine ⟨Current.sub_le_self G Λ M m, hmM0, ?_⟩
      rw [Current.sub_sub_self_of_le G Λ hmle]; exact hm0
    · intro m hm
      simp only [Finset.mem_filter, Current.mem_subFinset_iff] at hm
      exact Current.sub_sub_self_of_le G Λ hm.1
    · intro m hm
      simp only [Finset.mem_filter, Current.mem_subFinset_iff] at hm
      exact Current.sub_sub_self_of_le G Λ hm.1
    · intro m hm
      simp only [Finset.mem_filter, Current.mem_subFinset_iff] at hm
      obtain ⟨hmle, -⟩ := hm
      rw [Current.sub_sub_self_of_le G Λ hmle]; ring
  -- Peel the active edge and reindex `m' = m − 1_{e₀}` onto the defect filter.
  have step3 : (∑ m ∈ (Current.subFinset G Λ M).filter
        (fun m => m.sources G Λ = ∅ ∧ (M - m).sources G Λ = ∅),
        (m e₀ : ℝ) * (m.weight G Λ β J * (M - m).weight G Λ β J))
      = (β * J) * ∑ m ∈ (Current.subFinset G Λ (M - Current.fromEdgeFinset G Λ {e₀})).filter
          (fun m => m.sources G Λ = (e₀ : Sym2 ↑Λ).toFinset ∧
            ((M - Current.fromEdgeFinset G Λ {e₀}) - m).sources G Λ = ∅),
          m.weight G Λ β J *
            ((M - Current.fromEdgeFinset G Λ {e₀}) - m).weight G Λ β J := by
    -- Drop the vanishing `m e₀ = 0` terms.
    have hfilter : (∑ m ∈ (Current.subFinset G Λ M).filter
          (fun m => m.sources G Λ = ∅ ∧ (M - m).sources G Λ = ∅),
          (m e₀ : ℝ) * (m.weight G Λ β J * (M - m).weight G Λ β J))
        = ∑ m ∈ ((Current.subFinset G Λ M).filter
            (fun m => m.sources G Λ = ∅ ∧ (M - m).sources G Λ = ∅)).filter
            (fun m => 1 ≤ m e₀),
          (m e₀ : ℝ) * (m.weight G Λ β J * (M - m).weight G Λ β J) := by
      refine (Finset.sum_filter_of_ne ?_).symm
      intro m _ hne
      rcases Nat.eq_zero_or_pos (m e₀) with h0 | hp
      · exact absurd (by rw [h0]; simp) hne
      · exact hp
    rw [hfilter, Finset.mul_sum]
    refine Finset.sum_nbij' (fun m => m - Current.fromEdgeFinset G Λ {e₀})
      (fun m => m + Current.fromEdgeFinset G Λ {e₀}) ?_ ?_ ?_ ?_ ?_
    · -- forward: `m − 1_{e₀}` lands in the defect filter
      intro m hm
      simp only [Finset.mem_filter, Current.mem_subFinset_iff] at hm
      obtain ⟨⟨hmle, hm0, hmM0⟩, hme⟩ := hm
      have hpos : 0 < m e₀ := hme
      simp only [Finset.mem_filter, Current.mem_subFinset_iff]
      refine ⟨?_, ?_, ?_⟩
      · intro e; simp only [Current.sub_apply]
        exact Nat.sub_le_sub_right (hmle e) _
      · rw [Current.sources_sub_edge_symmDiff G Λ m e₀ hpos, hm0,
          ← Finset.bot_eq_empty, bot_symmDiff]
      · have hpt : (M - Current.fromEdgeFinset G Λ {e₀}) -
            (m - Current.fromEdgeFinset G Λ {e₀}) = M - m := by
          funext e
          simp only [Current.sub_apply, Current.fromEdgeFinset, Finset.mem_singleton]
          by_cases hee : e = e₀
          · have hle : m e₀ ≤ M e₀ := hmle e₀
            simp only [hee, ↓reduceIte]; omega
          · simp only [if_neg hee]; omega
        rw [hpt]; exact hmM0
    · -- backward: `m' + 1_{e₀}` lands in the sourcefree active filter
      intro m hm
      simp only [Finset.mem_filter, Current.mem_subFinset_iff] at hm
      obtain ⟨hmle, hmsrc, hmM0⟩ := hm
      simp only [Finset.mem_filter, Current.mem_subFinset_iff]
      have hround : (m + Current.fromEdgeFinset G Λ {e₀}) -
          Current.fromEdgeFinset G Λ {e₀} = m := by
        funext e; simp only [Current.sub_apply, Current.add_apply]; omega
      have hpe : 0 < (m + Current.fromEdgeFinset G Λ {e₀}) e₀ := by
        simp only [Current.add_apply, Current.fromEdgeFinset, Finset.mem_singleton,
          ↓reduceIte]; omega
      refine ⟨⟨?_, ?_, ?_⟩, hpe⟩
      · intro e
        have hle := hmle e
        simp only [Current.sub_apply, Current.fromEdgeFinset, Finset.mem_singleton] at hle
        simp only [Current.add_apply, Current.fromEdgeFinset, Finset.mem_singleton]
        by_cases hee : e = e₀
        · subst hee; simp only [↓reduceIte] at hle ⊢; omega
        · simp only [if_neg hee] at hle ⊢; omega
      · have hshift := Current.sources_sub_edge_symmDiff G Λ
          (m + Current.fromEdgeFinset G Λ {e₀}) e₀ hpe
        rw [hround] at hshift
        have hY : (m + Current.fromEdgeFinset G Λ {e₀}).sources G Λ
            = symmDiff (m.sources G Λ) (e₀ : Sym2 ↑Λ).toFinset := by
          rw [hshift]; exact (symmDiff_symmDiff_cancel_right _ _).symm
        rw [hY, hmsrc, symmDiff_self]; exact Finset.bot_eq_empty
      · have hpt : M - (m + Current.fromEdgeFinset G Λ {e₀})
            = (M - Current.fromEdgeFinset G Λ {e₀}) - m := by
          funext e; simp only [Current.sub_apply, Current.add_apply]; omega
        rw [hpt]; exact hmM0
    · -- left inverse: `(m − 1_{e₀}) + 1_{e₀} = m`
      intro m hm
      simp only [Finset.mem_filter, Current.mem_subFinset_iff] at hm
      obtain ⟨-, hme⟩ := hm
      have hEle : Current.fromEdgeFinset G Λ {e₀} ≤ m := by
        intro e; simp only [Current.fromEdgeFinset, Finset.mem_singleton]
        by_cases hee : e = e₀
        · subst hee; simp only [↓reduceIte]; omega
        · simp only [if_neg hee]; omega
      exact Current.sub_add_cancel_of_le G Λ hEle
    · -- right inverse: `(m' + 1_{e₀}) − 1_{e₀} = m'`
      intro m _
      funext e; simp only [Current.sub_apply, Current.add_apply]; omega
    · -- value: `(m e₀) w(m) w(M − m) = βJ · w(m − 1_{e₀}) w((M − 1_{e₀}) − (m − 1_{e₀}))`
      intro m hm
      simp only [Finset.mem_filter, Current.mem_subFinset_iff] at hm
      obtain ⟨⟨hmle, -⟩, hme⟩ := hm
      have hpos : 0 < m e₀ := hme
      have hne : (m e₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
      have hpt : (M - Current.fromEdgeFinset G Λ {e₀}) -
          (m - Current.fromEdgeFinset G Λ {e₀}) = M - m := by
        funext e
        simp only [Current.sub_apply, Current.fromEdgeFinset, Finset.mem_singleton]
        by_cases hee : e = e₀
        · have hle : m e₀ ≤ M e₀ := hmle e₀
          simp only [hee, ↓reduceIte]; omega
        · simp only [if_neg hee]; omega
      have hw := Current.weight_pred_edge G Λ β J m e₀ hpos
      rw [hpt, hw]
      field_simp
  rw [step1, step2, step3]; ring

set_option linter.unusedDecidableInType false in
/-- **Edge-pivotal event on a doubled current (Stage B2b, Candidate B)**: an edge
`e₀` is *pivotal for the pair `x, y` in the current `M`* when `x` and `y` are
connected in the support graph of `M` but become disconnected after *decrementing*
one copy of `e₀` (subtracting `1_{e₀} = Current.fromEdgeFinset G Λ {e₀}`):
`(M.toSimpleGraph G Λ).Reachable x y ∧
   ¬ ((M − 1_{e₀}).toSimpleGraph G Λ).Reachable x y`.
The decrement `M − 1_{e₀}` (rather than a simple-graph edge deletion) is the
correct multigraph semantics — it removes exactly one copy of `e₀` and keeps `e₀`
in the support whenever `M e₀ ≥ 2` — and it matches the reindexing target of the
Stage B2a defect summand `Current.doubledDefectSummand`. This is the graph event
whose probability appears in the per-edge excess: the difference
`E^{x↔y}[M e₀] − E^{∅,∅}[M e₀]` is intended (in the deferred B2c switching
identity) to equal `2βJ · ℙ^{x↔y}[e₀ pivotal]`, matching the
FFS Ch. 12 / Aizenman 1982 upper bound for Glimm–Jaffe Theorem 17.5.1
(issue #4386; the switching identity relating it to the defect summand is the
deferred brick B2c). -/
def Current.EdgePivotal (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) (M : Current G Λ) (x y : ↑Λ) : Prop :=
  (M.toSimpleGraph G Λ).Reachable x y ∧
    ¬ ((M - Current.fromEdgeFinset G Λ {e₀}).toSimpleGraph G Λ).Reachable x y

set_option linter.unusedDecidableInType false in
/-- **`Current.EdgePivotal` is decidable**: a noncomputable `Decidable` instance
via `Classical.propDecidable`, mirroring `Current.instDecidableAdj`. It is
logically valid on the finite doubled-current ensemble (unlocking the pivotal
indicator `if EdgePivotal … then 1 else 0` used to form the pivotal-restricted
sums), even though `Current.support` is noncomputable. -/
noncomputable instance Current.instDecidableEdgePivotal
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) (M : Current G Λ) (x y : ↑Λ) :
    Decidable (Current.EdgePivotal G Λ e₀ M x y) :=
  Classical.propDecidable _

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **An absent edge is never pivotal**: if `M e₀ = 0`, then `e₀` is not pivotal
for any pair `x, y` in `M`. Indeed `M e₀ = 0` forces `M − 1_{e₀} = M` (truncated
`Nat` subtraction at `e₀` gives `0 − 1 = 0`, and every other edge is unchanged),
so the two reachability clauses of `Current.EdgePivotal` become
`Reachable x y ∧ ¬ Reachable x y`, a contradiction. -/
theorem Current.not_edgePivotal_of_edge_eq_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) (M : Current G Λ) (x y : ↑Λ)
    (he : M e₀ = 0) :
    ¬ Current.EdgePivotal G Λ e₀ M x y := by
  intro hpiv
  obtain ⟨hR, hnr⟩ := hpiv
  have heq : M - Current.fromEdgeFinset G Λ {e₀} = M := by
    funext e
    simp only [Current.sub_apply, Current.fromEdgeFinset, Finset.mem_singleton]
    by_cases hee : e = e₀
    · subst hee; simp [he]
    · simp only [if_neg hee, Nat.sub_zero]
  rw [heq] at hnr
  exact hnr hR

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Cut-edge two-arms structure of a pivotal edge (Stage B2b)**: if `e₀ = s(a, b)`
is pivotal for `x, y` in `M`, then in the *decremented* support graph
`(M − 1_{e₀}).toSimpleGraph` the two vertices `x, y` reach opposite endpoints of
`e₀`: either `Reachable x a ∧ Reachable b y`, or `Reachable x b ∧ Reachable a y`.
This is the cut-edge decomposition that Stage B2c/B3 consume (the pivotal edge is
a bridge between the two arms carrying `x` and `y`).

Proof.  Let `D = M.toSimpleGraph.deleteEdges {s(a, b)}` be the *simple-graph*
deletion of the `a`–`b` edge.  Because subtraction only affects `e₀`, any
`D`-adjacency comes from a support edge `≠ e₀`, so `D ≤ (M − 1_{e₀}).toSimpleGraph`
(`hle`); it therefore suffices to produce the arms in `D` and lift them by
`SimpleGraph.Reachable.mono`.  A walk induction (`key`/`arm`) shows that if a
vertex `src` reaches neither `a` nor `b` in `D`, then every `M`-walk out of a
`D`-neighbourhood of `src` stays inside it — so, since `x` reaches `y` in `M` but
not in `D`, `x` must reach `a` or `b` in `D` (and symmetrically for `y`).  Mutual
exclusivity (`excl_a`/`excl_b`, via `¬ D.Reachable x y`) pairs the two arms across
`e₀`.  (FFS Ch. 12 / Aizenman 1982 Lemma 4.1; Glimm–Jaffe Theorem 17.5.1,
issue #4386.) -/
theorem Current.edgePivotal_arms
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) (M : Current G Λ) (x y a b : ↑Λ)
    (hab : (e₀ : Sym2 ↑Λ) = s(a, b))
    (hpiv : Current.EdgePivotal G Λ e₀ M x y) :
    (((M - Current.fromEdgeFinset G Λ {e₀}).toSimpleGraph G Λ).Reachable x a ∧
       ((M - Current.fromEdgeFinset G Λ {e₀}).toSimpleGraph G Λ).Reachable b y) ∨
    (((M - Current.fromEdgeFinset G Λ {e₀}).toSimpleGraph G Λ).Reachable x b ∧
       ((M - Current.fromEdgeFinset G Λ {e₀}).toSimpleGraph G Λ).Reachable a y) := by
  obtain ⟨hR, hnr⟩ := hpiv
  set D := (M.toSimpleGraph G Λ).deleteEdges {(e₀ : Sym2 ↑Λ)} with hDdef
  -- The simple-graph deletion of the `a`–`b` edge sits below the decremented graph.
  have hle : D ≤ (M - Current.fromEdgeFinset G Λ {e₀}).toSimpleGraph G Λ := by
    intro u v hadjD
    rw [hDdef, SimpleGraph.deleteEdges_adj] at hadjD
    obtain ⟨hG'adj, hnotin⟩ := hadjD
    rw [Current.toSimpleGraph_adj_iff] at hG'adj
    obtain ⟨hne, ed, hed, hu, hv⟩ := hG'adj
    rw [Current.toSimpleGraph_adj_iff]
    refine ⟨hne, ed, ?_, hu, hv⟩
    rw [Current.mem_support_iff] at hed ⊢
    by_cases hee : ed = e₀
    · exfalso
      apply hnotin
      have hsuv : (ed : Sym2 ↑Λ) = s(u, v) := (Sym2.mem_and_mem_iff hne).mp ⟨hu, hv⟩
      rw [Set.mem_singleton_iff, ← hsuv, hee]
    · rw [Current.sub_apply]
      simp only [Current.fromEdgeFinset, Finset.mem_singleton, if_neg hee, Nat.sub_zero]
      exact hed
  have hnrD : ¬ D.Reachable x y := fun h => hnr (h.mono hle)
  -- Each vertex reaches an endpoint of the pivotal edge in `D`.
  have arm : ∀ (src tgt : ↑Λ), (M.toSimpleGraph G Λ).Reachable src tgt →
      ¬ D.Reachable src tgt → D.Reachable src a ∨ D.Reachable src b := by
    intro src tgt hRc hnrc
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hna, hnb⟩ := hcon
    have key : ∀ (s t : ↑Λ), (M.toSimpleGraph G Λ).Walk s t →
        D.Reachable src s → D.Reachable src t := by
      intro s t w
      induction w with
      | nil => exact id
      | @cons u mid v hadj q ih =>
        intro hsrcu
        by_cases hcase : s(u, mid) = (e₀ : Sym2 ↑Λ)
        · exfalso
          have hmem : u = a ∨ u = b := by
            have h0 : u ∈ (e₀ : Sym2 ↑Λ) := by
              rw [← hcase]; exact Sym2.mem_iff.mpr (Or.inl rfl)
            rwa [hab, Sym2.mem_iff] at h0
          rcases hmem with rfl | rfl
          · exact hna hsrcu
          · exact hnb hsrcu
        · have hDadj : D.Adj u mid := by
            rw [hDdef]
            exact SimpleGraph.deleteEdges_adj.mpr
              ⟨hadj, by rw [Set.mem_singleton_iff]; exact hcase⟩
          exact ih (hsrcu.trans hDadj.reachable)
    obtain ⟨w⟩ := hRc
    exact hnrc (key src tgt w (SimpleGraph.Reachable.refl src))
  have hax := arm x y hR hnrD
  have hay := arm y x hR.symm (fun h => hnrD h.symm)
  have excl_a : ¬ (D.Reachable x a ∧ D.Reachable y a) :=
    fun ⟨h1, h2⟩ => hnrD (h1.trans h2.symm)
  have excl_b : ¬ (D.Reachable x b ∧ D.Reachable y b) :=
    fun ⟨h1, h2⟩ => hnrD (h1.trans h2.symm)
  rcases hax with hxa | hxb
  · rcases hay with hya | hyb
    · exact absurd ⟨hxa, hya⟩ excl_a
    · exact Or.inl ⟨hxa.mono hle, hyb.symm.mono hle⟩
  · rcases hay with hya | hyb
    · exact Or.inr ⟨hxb.mono hle, hya.symm.mono hle⟩
    · exact absurd ⟨hxb, hyb⟩ excl_b

set_option linter.unusedDecidableInType false in
/-- **Summability of the pivotal-restricted sourcefree summand (Stage B2b)**: for
`0 ≤ β`, `0 ≤ J` the map `M ↦ [e₀ pivotal for x, y in M] · D_β(M)` is `Summable`
over all doubled currents, where `[·]` is the `{0, 1}`-valued pivotal indicator
and `D_β` is the both-sourcefree doubled summand (`Current.doubledSourcefreeSummand`).
Since `0 ≤ [·] ≤ 1` and `D_β ≥ 0`, the term is dominated by `D_β`, which is
summable (`Current.summable_doubledSourcefree`); `Summable.of_nonneg_of_le`
concludes. This lets the next brick define the pivotal probability numerator
`∑'_{x↔y, e₀ pivotal} D_β`. (FFS Ch. 12; Glimm–Jaffe Theorem 17.5.1, issue #4386.) -/
theorem Current.summable_edgePivotal_doubledSourcefree
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] {β J : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (e₀ : (inducedGraph G Λ).edgeSet) (x y : ↑Λ) :
    Summable (fun M : Current G Λ =>
      (if Current.EdgePivotal G Λ e₀ M x y then (1 : ℝ) else 0)
        * Current.doubledSourcefreeSummand G Λ β J M) := by
  have hβJ : 0 ≤ β * J := mul_nonneg hβ hJ
  refine Summable.of_nonneg_of_le ?_ ?_ (Current.summable_doubledSourcefree G Λ hβJ)
  · intro M
    have hD := Current.doubledSourcefreeSummand_nonneg G Λ hβJ M
    split_ifs with h
    · simpa using hD
    · simp
  · intro M
    have hD := Current.doubledSourcefreeSummand_nonneg G Λ hβJ M
    split_ifs with h
    · simp
    · simpa using hD

set_option linter.unusedDecidableInType false in
/-- **Summability of the pivotal-restricted sourcefree summand over the reachable
ensemble (Stage B2b)**: the reachable-subtype version of
`Current.summable_edgePivotal_doubledSourcefree`. Over
`{M // (M.toSimpleGraph).Reachable x y}`, the map
`M ↦ [e₀ pivotal for x, y in M] · D_β(M)` is `Summable`, obtained from the
all-currents version by `Summable.comp_injective` along the injective inclusion
`Subtype.val`. This is the summable numerator of the `x↔y`-conditioned pivotal
probability. (FFS Ch. 12; Glimm–Jaffe Theorem 17.5.1, issue #4386.) -/
theorem Current.summable_edgePivotal_doubledSourcefree_reachable
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] {β J : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (e₀ : (inducedGraph G Λ).edgeSet) (x y : ↑Λ) :
    Summable (fun M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y} =>
      (if Current.EdgePivotal G Λ e₀ (M : Current G Λ) x y then (1 : ℝ) else 0)
        * Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ)) :=
  (Current.summable_edgePivotal_doubledSourcefree G Λ hβ hJ e₀ x y).comp_injective
    Subtype.val_injective

end Ambient
end IsingModel
