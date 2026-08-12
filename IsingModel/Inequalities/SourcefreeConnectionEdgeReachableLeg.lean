import IsingModel.Inequalities.SourcefreeConnectionEdgeEmptyLeg
import IsingModel.Inequalities.SourcefreeConnectionUnconditional
import IsingModel.RandomCurrent.Switching.GlobalSwitchingLimit

/-!
# Pivotal (reachable) leg of the per-edge switching identity (OZ Wall #2, Stage B2c, Step P1)

This file formalises **Step P1** of the *pivotal* (`x ↔ y`-conditioned) leg of the
per-edge switching identity underlying the *upper* (Ornstein–Zernike "Wall #2")
direction of the excess-current estimate for Glimm–Jaffe Theorem 17.5.1
(§17.5, p. 312; issue #4386, thread #4418).  Together with the clean leg
(`Current.doubledSourcefree_edgeExpectation_empty_eq`,
`SourcefreeConnectionEdgeEmptyLeg.lean`) it identifies the per-edge excess current
with the **truncated four-point ratio**
`E^{x↔y}[M e₀] − E^∅[M e₀] = 2βJ · (⟨σ_uσ_vσ_xσ_y⟩ − ⟨σ_uσ_v⟩⟨σ_xσ_y⟩) / ⟨σ_xσ_y⟩`,
which is the closing capstone of Step P1 (companion note
`rc-oz-stageB2c-switching-identity.tex`, §3.2-corrected, stages α–ε).

## Structure (companion note stages α–ε)

* **P1-δ** (`Current.reachable_add_edge_within_component_iff`): the only genuinely
  new (elementary) `SimpleGraph` lemma — adding one edge `e₀ = s(u, v)` inside a
  component (`u ↔ v` already) preserves *all* reachability.  Walk induction:
  `⇐` is `SimpleGraph.Reachable.mono`; `⇒` replaces each `e₀`-traversal by a fixed
  `u`–`v` walk.
* **Numerator identity** (`Current.tsum_reachable_edge_mul_doubledSourcefree_eq`):
  over the reachable ensemble,
  `∑'_{x↔y} (M e₀) D(M) = 2βJ · (weightSum ({u,v} △ {x,y}) · weightSum {x,y})`.
  Proof combines α (general-source character switch, P1-α =
  `Current.sum_jointFactor_source_eq_symmDiff_pair_of_reachable`), β (doubled-summand
  switch on the reachable event), γ (`C = ∅` factorization) and δ (edge-support
  reduction) through the clean-leg reindexing device `Current.edgeIncrementEquiv`.
* **Z-ratio capstone** (`Current.doubledSourcefree_edgeExcess_reachable_eq`):
  unconditional (coincidences absorbed by the `weightSum`-ratio form),
  `E^{x↔y}[M e₀] − E^∅[M e₀]
   = 2βJ · (weightSum ({u,v} △ {x,y})/weightSum {x,y} − weightSum {u,v}/weightSum ∅)`.
* **Truncated four-point capstone**
  (`Current.doubledSourcefree_edgeExcess_eq_truncated4pt`): for pairwise-distinct
  `u, v, x, y` (`Disjoint {u,v} {x,y}`) and `⟨σ_xσ_y⟩ ≠ 0`,
  `E^{x↔y}[M e₀] − E^∅[M e₀]
   = 2βJ · (⟨σ_uσ_vσ_xσ_y⟩ − ⟨σ_uσ_v⟩⟨σ_xσ_y⟩) / ⟨σ_xσ_y⟩`.

This completes **B2c Step P1** as an independent milestone.  Step P2 (the backbone
bijection identifying the truncated four-point ratio with the *graph*-pivotal
probability) is a separate research wall (Wall B3-grade) and is **not** treated
here.

## References

* Aizenman, M. (1982) Geometric analysis of φ⁴ fields, Lemma 3.2, p. 7,
  eq. (3.5) (the switching lemma).
* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality*
  (1992), Chapter 12.
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5 Theorem 17.5.1 (p. 312).

(Issue #4386, thread #4418.)
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **P1-δ: adding an edge within a component preserves reachability (Stage B2c)**:
for `u ≠ v` already connected in the support graph `K.toSimpleGraph` and an edge
`e₀ = s(u, v)`, adjoining one copy of `e₀` (`1_{e₀} = Current.fromEdgeFinset G Λ
{e₀}`) leaves the entire reachability relation unchanged: for all `x, y`,
`((K + 1_{e₀}).toSimpleGraph).Reachable x y ↔ (K.toSimpleGraph).Reachable x y`.

Proof.  `⇐` is `SimpleGraph.Reachable.mono` (`K ≤ K + 1_{e₀}` pointwise).  `⇒`: a
walk induction.  Any adjacency of `(K + 1_{e₀}).toSimpleGraph` comes from a support
edge `ed`; if `ed ≠ e₀` then `K ed ≠ 0`, so the same adjacency holds in
`K.toSimpleGraph`; if `ed = e₀` then the two endpoints are `{u, v}`, joined in
`K.toSimpleGraph` by hypothesis (`hRuv`).  Hence each edge of an `(K + 1_{e₀})`-walk
is reachable in `K.toSimpleGraph`, and transitivity closes the walk.  This is the
sole genuinely new `SimpleGraph` lemma of Step P1 (companion note
`rc-oz-stageB2c-switching-identity.tex`, Lemma P1-δ; elementary, not research).
(FFS Chapter 12; Glimm–Jaffe Theorem 17.5.1, issue #4386.) -/
theorem Current.reachable_add_edge_within_component_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (K : Current G Λ) (e₀ : (inducedGraph G Λ).edgeSet) (u v : ↑Λ)
    (huv : u ≠ v) (hab : (e₀ : Sym2 ↑Λ) = s(u, v))
    (hRuv : (K.toSimpleGraph G Λ).Reachable u v) (x y : ↑Λ) :
    ((K + Current.fromEdgeFinset G Λ {e₀}).toSimpleGraph G Λ).Reachable x y
      ↔ (K.toSimpleGraph G Λ).Reachable x y := by
  constructor
  · intro h
    have hstep : ∀ a b : ↑Λ,
        ((K + Current.fromEdgeFinset G Λ {e₀}).toSimpleGraph G Λ).Adj a b
          → (K.toSimpleGraph G Λ).Reachable a b := by
      intro a b hadj
      rw [Current.toSimpleGraph_adj_iff] at hadj
      obtain ⟨hne, ed, hed, ha, hb⟩ := hadj
      rw [Current.mem_support_iff, Current.add_apply] at hed
      by_cases hee : ed = e₀
      · subst hee
        rw [hab, Sym2.mem_iff] at ha hb
        rcases ha with rfl | rfl
        · rcases hb with rfl | rfl
          · exact absurd rfl hne
          · exact hRuv
        · rcases hb with rfl | rfl
          · exact hRuv.symm
          · exact absurd rfl hne
      · have hKed : K ed ≠ 0 := by
          simp only [Current.fromEdgeFinset, Finset.mem_singleton, if_neg hee,
            add_zero] at hed
          exact hed
        exact ((Current.toSimpleGraph_adj_iff G Λ K a b).mpr
          ⟨hne, ed, (Current.mem_support_iff G Λ K ed).mpr hKed, ha, hb⟩).reachable
    have key : ∀ (s t : ↑Λ),
        ((K + Current.fromEdgeFinset G Λ {e₀}).toSimpleGraph G Λ).Walk s t
          → (K.toSimpleGraph G Λ).Reachable s t := by
      intro s t w
      induction w with
      | nil => exact SimpleGraph.Reachable.refl _
      | cons hadj _ ih => exact (hstep _ _ hadj).trans ih
    obtain ⟨w⟩ := h
    exact key x y w
  · intro h
    refine h.mono (Current.toSimpleGraph_mono_of_le G Λ ?_)
    intro e
    rw [Current.add_apply]
    exact Nat.le_add_right _ _

set_option linter.unusedDecidableInType false in
/-- **Reachable-ensemble numerator identity (Stage B2c, Step P1)**: for
non-negative coupling `0 ≤ β J`, an edge `e₀ = s(u, v)` with `u ≠ v`, and
`x ≠ y`, the edge-weighted both-sourcefree doubled summand summed over the
reachable (`x ↔ y`) ensemble factorises,
`∑'_{M : x↔y} (M e₀) · D(M) = 2βJ · (weightSum ({u,v} △ {x,y}) · weightSum {x,y})`,
where `D(M) = Current.doubledSourcefreeSummand G Λ β J M`.

Proof (companion note stages α–ε).  Convert the reachable subtype sum to an
indicator-weighted sum over all currents (`tsum_subtype`) and restrict to
`{1 ≤ M e₀}`.  Stage B2a (`Current.edge_mul_doubledSourcefree_eq_defect`) turns each
term into `2βJ · χ(M) · D_{e₀}(M)`; unfolding `D_{e₀}(M) = H(M − 1_{e₀})` (the mixed
`({u,v}, ∅)`-sourced inner sum) and reindexing `M = K + 1_{e₀}` via
`Current.edgeIncrementEquiv` gives `2βJ · ∑'_K χ(K + 1_{e₀}) · H(K)`.  Then:
* **δ** — for `H(K) ≠ 0` one has `∂K = {u,v}`, hence `u ↔ v` in `G(K)`, so P1-δ
  (`Current.reachable_add_edge_within_component_iff`) replaces `χ(K + 1_{e₀})` by
  `χ(K)`;
* **β** — on the reachable event `H(K) = H'(K)` (the `({u,v} △ {x,y}, {x,y})`-sourced
  inner sum) by the general-source character switch P1-α
  (`Current.sum_jointFactor_source_eq_symmDiff_pair_of_reachable`), so
  `χ(K) H(K) = χ(K) H'(K)`;
* **γ** — `H'(K) ≠ 0` forces `x ↔ y` in `G(K)` (via
  `Current.reachable_of_subFinset_sources_pair`), so the indicator is redundant and
  `∑'_K χ(K) H'(K) = ∑'_K H'(K)`.

Finally the Stage A product identity
`Current.weightSum_mul_weightSum_eq_tsum_doubled_subFinset` (with `A = {u,v} △ {x,y}`,
`B = {x,y}`) identifies `∑'_K H'(K) = weightSum ({u,v} △ {x,y}) · weightSum {x,y}`.
(Aizenman 1982 Lemma 3.2, p. 7, eq. (3.5) / FFS Chapter 12; Glimm–Jaffe
Theorem 17.5.1, issue #4386.) -/
theorem Current.tsum_reachable_edge_mul_doubledSourcefree_eq
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (e₀ : (inducedGraph G Λ).edgeSet)
    (u v x y : ↑Λ) (huv : u ≠ v) (hxy : x ≠ y)
    (hab : (e₀ : Sym2 ↑Λ) = s(u, v)) :
    (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
        ((M : Current G Λ) e₀ : ℝ)
          * Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ))
      = 2 * (β * J)
        * (Current.weightSum G Λ (symmDiff ({u, v} : Finset ↑Λ) {x, y}) β J
            * Current.weightSum G Λ ({x, y} : Finset ↑Λ) β J) := by
  classical
  set D : Current G Λ → ℝ := Current.doubledSourcefreeSummand G Λ β J with hDdef
  set χ : Current G Λ → ℝ :=
    fun M => if (M.toSimpleGraph G Λ).Reachable x y then (1 : ℝ) else 0 with hχ
  set H : Current G Λ → ℝ := fun K =>
    ∑ m ∈ (Current.subFinset G Λ K).filter
        (fun m => m.sources G Λ = ({u, v} : Finset ↑Λ) ∧ (K - m).sources G Λ = ∅),
      m.weight G Λ β J * (K - m).weight G Λ β J with hH
  set H' : Current G Λ → ℝ := fun K =>
    ∑ m ∈ (Current.subFinset G Λ K).filter
        (fun m => m.sources G Λ = symmDiff ({u, v} : Finset ↑Λ) {x, y}
          ∧ (K - m).sources G Λ = ({x, y} : Finset ↑Λ)),
      m.weight G Λ β J * (K - m).weight G Λ β J with hH'
  have htf : (e₀ : Sym2 ↑Λ).toFinset = ({u, v} : Finset ↑Λ) := by
    rw [hab, Sym2.toFinset_mk_eq]
  -- The doubled defect summand is `H` reindexed by `M ↦ M − 1_{e₀}`.
  have hdefect : ∀ M : Current G Λ,
      Current.doubledDefectSummand G Λ e₀ β J M
        = H (M - Current.fromEdgeFinset G Λ {e₀}) := by
    intro M
    simp only [hH, Current.doubledDefectSummand, htf]
  -- Source support: `H(K) ≠ 0 ⟹ ∂K = {u,v}`.
  have hsrcH : ∀ K : Current G Λ, H K ≠ 0 → K.sources G Λ = ({u, v} : Finset ↑Λ) := by
    intro K hne
    simp only [hH] at hne
    obtain ⟨m, hmmem, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    rw [Finset.mem_filter, Current.mem_subFinset_iff] at hmmem
    obtain ⟨hmle, h1, h2⟩ := hmmem
    rw [Current.sub_sources_eq_symmDiff G Λ hmle, h1, ← Finset.bot_eq_empty,
      symmDiff_eq_bot] at h2
    exact h2
  -- Source support: `H'(K) ≠ 0 ⟹ ∂K = {u,v}`.
  have hsrcH' : ∀ K : Current G Λ, H' K ≠ 0 → K.sources G Λ = ({u, v} : Finset ↑Λ) := by
    intro K hne
    simp only [hH'] at hne
    obtain ⟨m, hmmem, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    rw [Finset.mem_filter, Current.mem_subFinset_iff] at hmmem
    obtain ⟨hmle, h1, h2⟩ := hmmem
    rw [Current.sub_sources_eq_symmDiff G Λ hmle, h1] at h2
    have h3 : K.sources G Λ
        = symmDiff ({x, y} : Finset ↑Λ) (symmDiff ({u, v} : Finset ↑Λ) {x, y}) := by
      have hcg := congrArg
        (fun s => symmDiff s (symmDiff ({u, v} : Finset ↑Λ) {x, y})) h2
      simpa [symmDiff_symmDiff_cancel_right] using hcg
    rw [h3, symmDiff_comm ({u, v} : Finset ↑Λ) {x, y}, symmDiff_symmDiff_cancel_left]
  -- `H(K) ≠ 0 ⟹ u ↔ v` in `G(K)` (needed for P1-δ).
  have hHreach_uv : ∀ K : Current G Λ, H K ≠ 0 → (K.toSimpleGraph G Λ).Reachable u v :=
    fun K hne => Current.sources_reachable_of_sources_eq_pair G Λ K huv (hsrcH K hne)
  -- `H'(K) ≠ 0 ⟹ x ↔ y` in `G(K)` (needed for γ).
  have hH'reach_xy : ∀ K : Current G Λ, H' K ≠ 0 → (K.toSimpleGraph G Λ).Reachable x y := by
    intro K hne
    simp only [hH'] at hne
    obtain ⟨m, hmmem, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    rw [Finset.mem_filter, Current.mem_subFinset_iff] at hmmem
    obtain ⟨-, -, h2⟩ := hmmem
    exact Current.reachable_of_subFinset_sources_pair G Λ hxy
      ((Current.mem_subFinset_iff G Λ K (K - m)).mpr (Current.sub_le_self G Λ K m)) h2
  -- β: `H(K) = H'(K)` on the reachable event.
  have hHH' : ∀ K : Current G Λ, (K.toSimpleGraph G Λ).Reachable x y → H K = H' K := by
    intro K hreachK
    by_cases hK : K.sources G Λ = ({u, v} : Finset ↑Λ)
    · have key : ∀ (A B : Finset ↑Λ), K.sources G Λ = symmDiff A B →
          (∑ m ∈ (Current.subFinset G Λ K).filter
              (fun m => m.sources G Λ = A ∧ (K - m).sources G Λ = B),
            m.weight G Λ β J * (K - m).weight G Λ β J)
            = K.weight G Λ β J
                * ∑ m ∈ Current.subFinset_with_source G Λ K A,
                    Current.jointFactor G Λ m (K - m) := by
        intro A B hAB
        have hfilter : (Current.subFinset G Λ K).filter
              (fun m => m.sources G Λ = A ∧ (K - m).sources G Λ = B)
            = Current.subFinset_with_source G Λ K A := by
          unfold Current.subFinset_with_source
          refine Finset.filter_congr (fun m hm => ?_)
          rw [Current.mem_subFinset_iff] at hm
          unfold Current.HasSources
          constructor
          · rintro ⟨h1, _⟩; exact h1
          · intro h1
            refine ⟨h1, ?_⟩
            rw [Current.sub_sources_eq_symmDiff G Λ hm, hAB, h1, symmDiff_comm A B,
              symmDiff_assoc, symmDiff_self, symmDiff_bot]
        rw [hfilter, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m hm => ?_)
        rw [Current.mem_subFinset_with_source_iff] at hm
        rw [Current.weight_mul_weight_eq_weight_add_mul_jointFactor,
          Current.add_sub_cancel_of_le G Λ hm.1]
      simp only [hH, hH']
      rw [key ({u, v} : Finset ↑Λ) ∅
            (by rw [hK, ← Finset.bot_eq_empty, symmDiff_bot]),
        key (symmDiff ({u, v} : Finset ↑Λ) {x, y}) {x, y}
            (by rw [hK, symmDiff_assoc, symmDiff_self, symmDiff_bot])]
      congr 1
      exact Current.sum_jointFactor_source_eq_symmDiff_pair_of_reachable
        G Λ K hxy ({u, v} : Finset ↑Λ) hreachK
    · have hHz : H K = 0 := by
        by_contra hcon; exact hK (hsrcH K hcon)
      have hH'z : H' K = 0 := by
        by_contra hcon; exact hK (hsrcH' K hcon)
      rw [hHz, hH'z]
  -- Support of the indicator-weighted numerator is within `{1 ≤ M e₀}`.
  have hsupp : Function.support
      (fun M : Current G Λ => χ M * ((M e₀ : ℝ) * D M)) ⊆ {M : Current G Λ | 1 ≤ M e₀} := by
    intro M hM
    rw [Function.mem_support] at hM
    by_contra hcon
    simp only [Set.mem_setOf_eq, not_le, Nat.lt_one_iff] at hcon
    apply hM
    simp [hcon]
  -- Convert the reachable subtype sum to the indicator-weighted sum.
  have hsubtype_eq :
      (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
          ((M : Current G Λ) e₀ : ℝ) * D (M : Current G Λ))
        = ∑' M : Current G Λ, χ M * ((M e₀ : ℝ) * D M) := by
    rw [show (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
            ((M : Current G Λ) e₀ : ℝ) * D (M : Current G Λ))
          = ∑' M : Current G Λ,
            ({M : Current G Λ | (M.toSimpleGraph G Λ).Reachable x y}).indicator
              (fun N : Current G Λ => (N e₀ : ℝ) * D N) M
        from tsum_subtype {M : Current G Λ | (M.toSimpleGraph G Λ).Reachable x y}
          (fun N : Current G Λ => (N e₀ : ℝ) * D N)]
    refine tsum_congr (fun M => ?_)
    rw [Set.indicator_apply]
    by_cases hR : (M.toSimpleGraph G Λ).Reachable x y
    · simp only [hχ, Set.mem_setOf_eq, hR, if_true, one_mul]
    · simp only [hχ, Set.mem_setOf_eq, hR, if_false, zero_mul]
  rw [hsubtype_eq]
  calc ∑' M : Current G Λ, χ M * ((M e₀ : ℝ) * D M)
      = ∑' x' : {M : Current G Λ // 1 ≤ M e₀},
          χ (x' : Current G Λ)
            * (((x' : Current G Λ) e₀ : ℝ) * D (x' : Current G Λ)) :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' x' : {M : Current G Λ // 1 ≤ M e₀},
          2 * (β * J) * (χ (x' : Current G Λ)
            * Current.doubledDefectSummand G Λ e₀ β J (x' : Current G Λ)) := by
        refine tsum_congr (fun x' => ?_)
        rw [hDdef, Current.edge_mul_doubledSourcefree_eq_defect G Λ β J
          (x' : Current G Λ) e₀ x'.2]
        ring
    _ = 2 * (β * J) * ∑' x' : {M : Current G Λ // 1 ≤ M e₀},
          χ (x' : Current G Λ)
            * Current.doubledDefectSummand G Λ e₀ β J (x' : Current G Λ) := tsum_mul_left
    _ = 2 * (β * J) * ∑' x' : {M : Current G Λ // 1 ≤ M e₀},
          χ (x' : Current G Λ)
            * H ((x' : Current G Λ) - Current.fromEdgeFinset G Λ {e₀}) := by
        congr 1
        refine tsum_congr (fun x' => ?_)
        rw [hdefect (x' : Current G Λ)]
    _ = 2 * (β * J) * ∑' K : Current G Λ,
          χ (K + Current.fromEdgeFinset G Λ {e₀}) * H K := by
        congr 1
        rw [← Equiv.tsum_eq (Current.edgeIncrementEquiv G Λ e₀)
          (fun K => χ (K + Current.fromEdgeFinset G Λ {e₀}) * H K)]
        refine tsum_congr (fun x' => ?_)
        have hEle : Current.fromEdgeFinset G Λ {e₀} ≤ (x' : Current G Λ) := by
          intro e
          simp only [Current.fromEdgeFinset, Finset.mem_singleton]
          by_cases hee : e = e₀
          · subst hee; simpa using x'.2
          · simp only [if_neg hee]; omega
        have hrec : ((x' : Current G Λ) - Current.fromEdgeFinset G Λ {e₀})
              + Current.fromEdgeFinset G Λ {e₀} = (x' : Current G Λ) :=
          Current.sub_add_cancel_of_le G Λ hEle
        have hcoe : (Current.edgeIncrementEquiv G Λ e₀) x'
            = (x' : Current G Λ) - Current.fromEdgeFinset G Λ {e₀} := rfl
        simp only [hcoe, hrec]
    _ = 2 * (β * J) * ∑' K : Current G Λ, χ K * H K := by
        congr 1
        refine tsum_congr (fun K => ?_)
        by_cases hHK : H K = 0
        · rw [hHK, mul_zero, mul_zero]
        · have hchi : χ (K + Current.fromEdgeFinset G Λ {e₀}) = χ K := by
            simp only [hχ]
            exact if_congr
              (Current.reachable_add_edge_within_component_iff G Λ K e₀ u v huv hab
                (hHreach_uv K hHK) x y) rfl rfl
          rw [hchi]
    _ = 2 * (β * J) * ∑' K : Current G Λ, χ K * H' K := by
        congr 1
        refine tsum_congr (fun K => ?_)
        by_cases hRK : (K.toSimpleGraph G Λ).Reachable x y
        · rw [hHH' K hRK]
        · have hz : χ K = 0 := by simp only [hχ, if_neg hRK]
          rw [hz, zero_mul, zero_mul]
    _ = 2 * (β * J) * ∑' K : Current G Λ, H' K := by
        congr 1
        refine tsum_congr (fun K => ?_)
        by_cases hH'K : H' K = 0
        · rw [hH'K, mul_zero]
        · have hz : χ K = 1 := by simp only [hχ, if_pos (hH'reach_xy K hH'K)]
          rw [hz, one_mul]
    _ = 2 * (β * J)
          * (Current.weightSum G Λ (symmDiff ({u, v} : Finset ↑Λ) {x, y}) β J
              * Current.weightSum G Λ ({x, y} : Finset ↑Λ) β J) := by
        congr 1
        simp only [hH']
        exact (Current.weightSum_mul_weightSum_eq_tsum_doubled_subFinset
          G Λ (symmDiff ({u, v} : Finset ↑Λ) {x, y}) {x, y} hβJ).symm

set_option linter.unusedDecidableInType false in
/-- **Z-ratio capstone (Stage B2c, Step P1): per-edge excess as a `weightSum`
ratio**: for `0 ≤ β J`, an edge `e₀ = s(u, v)` with `u ≠ v`, and `x ≠ y`, the
per-edge contribution to the excess current (the summand of
`Current.doubledSourcefree_excess_eq_sum_edge`) equals
\[
  \frac{\sum_{x↔y}(M e₀)D}{\sum_{x↔y}D} - \frac{\sum_M (M e₀)D}{\sum_M D}
    = 2βJ\Big(\frac{Z_{\{u,v\}△\{x,y\}}}{Z_{\{x,y\}}} - \frac{Z_{\{u,v\}}}{Z_\emptyset}\Big),
\]
with `Z_A = Current.weightSum G Λ A β J` and `D = Current.doubledSourcefreeSummand`.

Proof.  The reachable numerator is `2βJ · Z_{{u,v}△{x,y}} · Z_{x,y}`
(`Current.tsum_reachable_edge_mul_doubledSourcefree_eq`), the reachable
denominator is `Z_{x,y}²` (from the unconditional connection representation
`Current.correlation_sq_mul_weightSum_empty_sq_eq_tsum_reachable_sourcefree_uncond`
together with `⟨σ_xσ_y⟩ = Z_{x,y}/Z_∅` and `Z_∅ > 0`), the all-current numerator is
`2βJ · Z_{u,v} · Z_∅` (`Current.tsum_edge_mul_doubledSourcefree_eq`, clean leg), and
the all-current denominator is `Z_∅²` (U1).  The algebraic identity
`num · p / p² = num / p` (total division, so coincidence cases `Z_{x,y} = 0` are
absorbed) closes the goal.  This is the unconditional form of the truncated
four-point ratio (companion note `rc-oz-stageB2c-switching-identity.tex`,
§3.2-corrected eq. (4pt); Aizenman 1982 Lemma 3.2, p. 7, eq. (3.5)).
(Glimm–Jaffe Theorem 17.5.1, issue #4386.) -/
theorem Current.doubledSourcefree_edgeExcess_reachable_eq
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (e₀ : (inducedGraph G Λ).edgeSet)
    (u v x y : ↑Λ) (huv : u ≠ v) (hxy : x ≠ y)
    (hab : (e₀ : Sym2 ↑Λ) = s(u, v)) :
    (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
          ((M : Current G Λ) e₀ : ℝ)
            * Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ))
        / ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
            Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ)
      - (∑' M : Current G Λ,
            (M e₀ : ℝ) * Current.doubledSourcefreeSummand G Λ β J M)
          / ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M
      = 2 * (β * J)
        * (Current.weightSum G Λ (symmDiff ({u, v} : Finset ↑Λ) {x, y}) β J
              / Current.weightSum G Λ ({x, y} : Finset ↑Λ) β J
            - Current.weightSum G Λ ({u, v} : Finset ↑Λ) β J
              / Current.weightSum G Λ ∅ β J) := by
  have hZ : 0 < Current.weightSum G Λ ∅ β J := Current.weightSum_empty_pos G Λ hβJ
  have hfrac : ∀ (num p : ℝ), num * p / p ^ 2 = num / p := by
    intro num p
    rcases eq_or_ne p 0 with h | h
    · subst h; simp
    · rw [pow_two, mul_div_mul_right num p h]
  have hden_all : (∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M)
      = Current.weightSum G Λ ∅ β J ^ 2 :=
    (Current.weightSum_empty_sq_eq_tsum_doubled_sourcefree G Λ hβJ).symm
  have hcorr : correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y}
        * Current.weightSum G Λ ∅ β J = Current.weightSum G Λ {x, y} β J := by
    rw [correlation_inducedGraph_eq_weightSum_ratio G Λ hβJ {x, y},
      div_mul_cancel₀ _ hZ.ne']
  have hden_reach : (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
        Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ))
      = Current.weightSum G Λ {x, y} β J ^ 2 := by
    rw [← Current.correlation_sq_mul_weightSum_empty_sq_eq_tsum_reachable_sourcefree_uncond
        G Λ hxy hβJ, ← mul_pow, hcorr]
  rw [Current.tsum_reachable_edge_mul_doubledSourcefree_eq G Λ hβJ e₀ u v x y huv hxy hab,
    Current.tsum_edge_mul_doubledSourcefree_eq G Λ hβJ e₀ u v hab, hden_reach, hden_all,
    show 2 * (β * J)
          * (Current.weightSum G Λ (symmDiff ({u, v} : Finset ↑Λ) {x, y}) β J
              * Current.weightSum G Λ {x, y} β J)
        = (2 * (β * J) * Current.weightSum G Λ (symmDiff ({u, v} : Finset ↑Λ) {x, y}) β J)
            * Current.weightSum G Λ {x, y} β J from by ring,
    show 2 * (β * J)
          * (Current.weightSum G Λ {u, v} β J * Current.weightSum G Λ ∅ β J)
        = (2 * (β * J) * Current.weightSum G Λ {u, v} β J)
            * Current.weightSum G Λ ∅ β J from by ring,
    hfrac _ (Current.weightSum G Λ {x, y} β J),
    hfrac _ (Current.weightSum G Λ ∅ β J)]
  ring

set_option linter.unusedDecidableInType false in
/-- **Truncated four-point capstone (Stage B2c, Step P1)**: for `0 ≤ β J`, an edge
`e₀ = s(u, v)` with `u ≠ v`, `x ≠ y`, `u, v` disjoint from `x, y`
(`Disjoint {u,v} {x,y}`), and non-vanishing two-point function
`⟨σ_xσ_y⟩ ≠ 0`, the per-edge excess current is the *truncated four-point ratio*
\[
  \frac{\sum_{x↔y}(M e₀)D}{\sum_{x↔y}D} - \frac{\sum_M (M e₀)D}{\sum_M D}
    = 2βJ\,\frac{\langle\sigma_u\sigma_v\sigma_x\sigma_y\rangle
        - \langle\sigma_u\sigma_v\rangle\langle\sigma_x\sigma_y\rangle}
       {\langle\sigma_x\sigma_y\rangle}.
\]
This is the closing capstone of Step P1 (companion note
`rc-oz-stageB2c-switching-identity.tex`, §3.2-corrected eq. (truncated); Aizenman
1982 Lemma 3.2, p. 7, eq. (3.5), which switches the sources producing the
truncated correlation).

Proof.  From the `weightSum`-ratio form
(`Current.doubledSourcefree_edgeExcess_reachable_eq`), the disjointness gives
`{u,v} △ {x,y} = {u,v,x,y}` (`Disjoint.symmDiff_eq_sup`), and each `weightSum` is
rewritten as `⟨·⟩ · Z_∅` via `correlation_inducedGraph_eq_weightSum_ratio`
(`Z_∅ > 0`); the ratio algebra closes by `field_simp` (`⟨σ_xσ_y⟩ ≠ 0`, `Z_∅ > 0`)
and `ring`.  The distinctness (`Disjoint`) and non-vanishing hypotheses are exactly
where the `⟨·⟩`-form differs from the unconditional `weightSum`-ratio form.
(Glimm–Jaffe Theorem 17.5.1, issue #4386.) -/
theorem Current.doubledSourcefree_edgeExcess_eq_truncated4pt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (e₀ : (inducedGraph G Λ).edgeSet)
    (u v x y : ↑Λ) (huv : u ≠ v) (hxy : x ≠ y)
    (hab : (e₀ : Sym2 ↑Λ) = s(u, v))
    (hdisj : Disjoint ({u, v} : Finset ↑Λ) {x, y})
    (hc2 : correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y} ≠ 0) :
    (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
          ((M : Current G Λ) e₀ : ℝ)
            * Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ))
        / ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
            Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ)
      - (∑' M : Current G Λ,
            (M e₀ : ℝ) * Current.doubledSourcefreeSummand G Λ β J M)
          / ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M
      = 2 * (β * J)
        * (correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {u, v, x, y}
            - correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {u, v}
              * correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y})
          / correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y} := by
  have hZ : 0 < Current.weightSum G Λ ∅ β J := Current.weightSum_empty_pos G Λ hβJ
  have hAeq : symmDiff ({u, v} : Finset ↑Λ) {x, y} = {u, v, x, y} := by
    rw [hdisj.symmDiff_eq_sup, Finset.sup_eq_union]
    ext a
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [Current.doubledSourcefree_edgeExcess_reachable_eq G Λ hβJ e₀ u v x y huv hxy hab,
    hAeq, correlation_inducedGraph_eq_weightSum_ratio G Λ hβJ {u, v, x, y},
    correlation_inducedGraph_eq_weightSum_ratio G Λ hβJ {u, v},
    correlation_inducedGraph_eq_weightSum_ratio G Λ hβJ {x, y}]
  have hp : Current.weightSum G Λ {x, y} β J ≠ 0 := by
    intro h0
    apply hc2
    rw [correlation_inducedGraph_eq_weightSum_ratio G Λ hβJ {x, y}, h0, zero_div]
  field_simp

end Ambient

end IsingModel
