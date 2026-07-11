import IsingModel.Inequalities.SourcefreeConnectionRepresentation
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

end Ambient
end IsingModel
