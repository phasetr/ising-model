import IsingModel.AmbientLattice.TruncatedFunctions
import IsingModel.Inequalities.SimonLieb
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Infinite-volume Simon-Lieb high-temperature bounds

Nonnegativity and infinite-volume Simon-Lieb wrappers at `h = 0`.

References: B. Simon, *Correlation inequalities and the decay of correlations in
ferromagnets*, Comm. Math. Phys. 77 (1980), 111–126; E. H. Lieb, *A refinement of
Simon's correlation inequality*, Comm. Math. Phys. 77 (1980), 127–135.
-/

namespace IsingModel.Ambient

variable {V : Type*} [DecidableEq V]

/-- **Nonnegativity of `correlationInfinite`** for `0 ≤ β * J`:
at `h = 0`, the correlation is ≥ 0, derived from the per-stage nonnegativity
(via `correlation_inducedGraph_eq_weightSum_ratio` + `Current.weightSum_nonneg`)
and `le_ciSup`. Unlike `correlationInfinite_nonneg`, this requires only `0 ≤ β * J`
rather than full `Ferromagnetic` structure. -/
lemma correlationInfinite_nonneg_of_hβJ
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (A : Finset V) :
    0 ≤ correlationInfinite G Λ ⟨J, 0, β⟩ A := by
  classical
  rw [correlationInfinite_eq_ciSup]
  apply le_ciSup_of_le (correlationAlongExhaustion_bddAbove G Λ _ A) 0
  by_cases hA0 : A ⊆ Λ.volume 0
  · rw [correlationAlongExhaustion_of_subset G Λ _ hA0, correlationΛ_apply]
    rw [correlation_inducedGraph_eq_weightSum_ratio G (Λ.volume 0) hβJ]
    have hZ : 0 < IsingModel.partitionFunction (inducedGraph G (Λ.volume 0))
        (⟨J, 0, β⟩ : IsingParams ℝ) :=
      IsingModel.partitionFunction_pos _ _
    rw [partitionFunction_inducedGraph_eq_pow_card_mul_weightSum_empty G (Λ.volume 0) hβJ] at hZ
    have h2 : (0 : ℝ) < (2 : ℝ) ^ Fintype.card (↑(Λ.volume 0) : Type _) := by positivity
    have hWpos : 0 < Current.weightSum G (Λ.volume 0) ∅ β J :=
      (mul_pos_iff.mp hZ).elim (·.2) (fun h => absurd h2 (not_lt.mpr h.1.le))
    exact div_nonneg (Current.weightSum_nonneg G (Λ.volume 0) _ hβJ) hWpos.le
  · rw [correlationAlongExhaustion_of_not_subset G Λ _ hA0]

set_option maxHeartbeats 800000 in
-- The proof involves `ciSup_le` + `sum_le_sum` + `Finset.sum_image` injectivity,
-- requiring extended heartbeats beyond the default 200000 limit.
open SimpleGraph in
/-- **∞-volume Simon-Lieb inequality** (Simon 1980; Lieb 1980):
for `h = 0`, `0 ≤ βJ`, and `i` not adjacent to `j` in `G`,
`⟨σ_iσ_j⟩_∞ ≤ βJ · ∑_{k~i} ⟨σ_kσ_j⟩_∞`.

The hypothesis `hnadj : ¬G.Adj i j` excludes the self-correlation issue:
when `G.Adj i j`, the Simon-Lieb term for the edge `{i,j}` is `⟨σ^∅⟩ = 1`,
but in this formalization `correlationInfinite G Λ p {j,j} = 0`
(since `{j,j} = {j}` as a Finset, giving magnetization = 0 at h = 0).

Proof: `ciSup_le` + per-stage finite-vol Simon-Lieb + monotone convergence.

Reference: Simon 1980, Comm. Math. Phys. 77, 111–126; Lieb 1980, Comm. Math.
Phys. 77, 127–135. -/
theorem correlationInfinite_simon_lieb
    (G : SimpleGraph V) [G.LocallyFinite]
    (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    {i j : V} (hij : i ≠ j) (hnadj : ¬G.Adj i j) :
    correlationInfinite G Λ ⟨J, 0, β⟩ {i, j}
      ≤ β * J *
          ∑ k ∈ G.neighborFinset i,
            correlationInfinite G Λ ⟨J, 0, β⟩ {k, j} := by
  classical
  -- Reduce to per-stage bounds via ciSup_le
  rw [correlationInfinite_eq_ciSup]
  apply ciSup_le
  intro n
  -- Case split: {i,j} ⊆ Λ.volume n or not
  by_cases hA : ({i, j} : Finset V) ⊆ Λ.volume n
  · -- Main case: both i,j ∈ Λ.volume n
    have hi : i ∈ Λ.volume n :=
      hA (Finset.mem_insert_self i {j})
    have hj : j ∈ Λ.volume n :=
      hA (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self j)))
    -- Rewrite correlationAlongExhaustion via correlationΛ_apply
    rw [correlationAlongExhaustion_of_subset G Λ _ hA, correlationΛ_apply]
    -- Identify liftFinset {i,j} = {⟨i,hi⟩, ⟨j,hj⟩}
    have h_lift : liftFinset ({i, j} : Finset V) hA
        = ({⟨i, hi⟩, ⟨j, hj⟩} : Finset ↑(Λ.volume n)) := by
      ext ⟨x, _⟩; simp [mem_liftFinset, Subtype.ext_iff]
    rw [h_lift]
    -- ⟨i,hi⟩ ≠ ⟨j,hj⟩ in ↑(Λ.volume n)
    have hij' : (⟨i, hi⟩ : ↑(Λ.volume n)) ≠ ⟨j, hj⟩ :=
      fun h => hij (congr_arg Subtype.val h)
    -- Helper: extract G-adjacency from (inducedGraph G Λn)-edge membership at ⟨i,hi⟩
    have get_adj : ∀ (e : (inducedGraph G (Λ.volume n)).edgeSet)
        (hei : (⟨i, hi⟩ : ↑(Λ.volume n)) ∈ (e : Sym2 ↑(Λ.volume n))),
        G.Adj i (Sym2.Mem.other hei).val := by
      intro e hei
      -- Sym2.other_spec hei : s(⟨i,hi⟩, Sym2.Mem.other hei) = (e : Sym2 ...)
      -- (Sym2.other_spec hei).symm : (e : Sym2 ...) = s(⟨i,hi⟩, u)
      have h_mem : s((⟨i, hi⟩ : ↑(Λ.volume n)), Sym2.Mem.other hei) ∈
          (inducedGraph G (Λ.volume n)).edgeSet :=
        (Sym2.other_spec hei).symm ▸ e.prop
      simp only [inducedGraph_apply, SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj] at h_mem
      exact h_mem
    -- Apply finite-volume Simon-Lieb and bound the edge sum by the neighbor sum
    apply le_trans (correlation_inducedGraph_simon_lieb G (Λ.volume n) hβJ hij')
    apply mul_le_mul_of_nonneg_left _ hβJ
    -- For each edge e ∈ filter (incident to ⟨i,hi⟩), let u := Sym2.Mem.other hei:
    --   corr(symmDiff {⟨i,hi⟩,⟨j,hj⟩} e.toFinset) = corr{u, ⟨j,hj⟩} ≤ corrInf{u.val, j}
    --   and u.val ∈ G.neighborFinset i
    -- Step 1: pointwise bound for each edge in filter
    have h_each : ∀ (e : (inducedGraph G (Λ.volume n)).edgeSet)
        (hei : (⟨i, hi⟩ : ↑(Λ.volume n)) ∈ (e : Sym2 ↑(Λ.volume n))),
        correlation (inducedGraph G (Λ.volume n)) (⟨J, 0, β⟩ : IsingParams ℝ)
            (symmDiff {(⟨i, hi⟩ : ↑(Λ.volume n)), ⟨j, hj⟩}
              (e : Sym2 ↑(Λ.volume n)).toFinset)
          ≤ correlationInfinite G Λ ⟨J, 0, β⟩ {(Sym2.Mem.other hei).val, j} := by
      intro e hei
      set u := Sym2.Mem.other hei with hu_def
      have hiu : (⟨i, hi⟩ : ↑(Λ.volume n)) ≠ u :=
        (Sym2.other_ne (SimpleGraph.not_isDiag_of_mem_edgeSet _ e.prop) hei).symm
      have he_toFinset : (e : Sym2 ↑(Λ.volume n)).toFinset =
          {(⟨i, hi⟩ : ↑(Λ.volume n)), u} := by
        have h := @Sym2.toFinset_mk_eq _ _ (⟨i, hi⟩ : ↑(Λ.volume n)) u
        rwa [Sym2.other_spec hei] at h
      have huj_val : u.val ≠ j := by
        intro heq
        exact hnadj (heq ▸ get_adj e hei)
      rw [he_toFinset,
        symmDiff_pair_pair_of_ne hij' hiu
          (fun h => huj_val (congr_arg Subtype.val h))]
      -- corr{u, ⟨j,hj⟩} = correlationAlongExhaustion G Λ p {u.val, j} n
      have h_uj_sub : ({u.val, j} : Finset V) ⊆ Λ.volume n :=
        Finset.insert_subset_iff.mpr ⟨u.prop, Finset.singleton_subset_iff.mpr hj⟩
      have h_lift2 : liftFinset ({u.val, j} : Finset V) h_uj_sub
          = ({u, (⟨j, hj⟩ : ↑(Λ.volume n))} : Finset ↑(Λ.volume n)) := by
        ext ⟨x, _⟩; simp [mem_liftFinset, Subtype.ext_iff]
      have h_corr_eq :
          correlation (inducedGraph G (Λ.volume n)) (⟨J, 0, β⟩ : IsingParams ℝ)
              ({u, (⟨j, hj⟩ : ↑(Λ.volume n))} : Finset ↑(Λ.volume n))
            = correlationAlongExhaustion G Λ ⟨J, 0, β⟩ {u.val, j} n := by
        rw [correlationAlongExhaustion_of_subset G Λ _ h_uj_sub,
            correlationΛ_apply, h_lift2]
      rw [h_corr_eq]
      exact correlationAlongExhaustion_le_correlationInfinite G Λ _ {u.val, j} n
    -- Step 2: apply the pointwise bounds and map edge filter to neighbor sum
    set filt := Finset.univ.filter (fun e : (inducedGraph G (Λ.volume n)).edgeSet =>
      (⟨i, hi⟩ : ↑(Λ.volume n)) ∈ (e : Sym2 ↑(Λ.volume n)))
    -- Sub-step 2a: ∑ e ∈ filt, symmDiffCorr(e) ≤ ∑ ⟨e,he⟩ ∈ filt.attach, corrInf{other_e, j}
    apply le_trans (b := ∑ e ∈ filt.attach,
        correlationInfinite G Λ ⟨J, 0, β⟩
          {(Sym2.Mem.other ((Finset.mem_filter.mp e.prop).2)).val, j})
    · rw [← Finset.sum_attach filt]
      apply Finset.sum_le_sum
      intro e _
      exact h_each e.val (Finset.mem_filter.mp e.prop).2
    -- Sub-step 2b: ∑ ⟨e,he⟩ ∈ filt.attach, corrInf{other_e, j} ≤ ∑ k ∈ nbrFinset, corrInf{k,j}
    -- Map filt.attach to G.neighborFinset i injectively via ⟨e,he⟩ ↦ (other hei).val
    apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg
        (s := filt.attach.image (fun e =>
            (Sym2.Mem.other ((Finset.mem_filter.mp e.prop).2)).val))
        (Finset.image_subset_iff.mpr fun ⟨e, he⟩ _ => by
          rw [G.mem_neighborFinset]
          simp only [filt, Finset.mem_filter, Finset.mem_univ, true_and] at he
          exact get_adj e he)
        (fun k _ _ => correlationInfinite_nonneg_of_hβJ G Λ hβJ {k, j}))
    rw [Finset.sum_image]
    intro ⟨e1, he1⟩ _ ⟨e2, he2⟩ _ h
    have hei1 := (Finset.mem_filter.mp he1).2
    have hei2 := (Finset.mem_filter.mp he2).2
    have h_sub : Sym2.Mem.other hei1 = Sym2.Mem.other hei2 := Subtype.ext h
    simp only [Subtype.mk.injEq]
    apply Subtype.val_injective
    exact (Sym2.other_spec hei1).symm.trans (h_sub ▸ Sym2.other_spec hei2)
  · -- Not-subset case: LHS = 0 ≤ RHS
    rw [correlationAlongExhaustion_of_not_subset G Λ _ hA]
    exact mul_nonneg hβJ
      (Finset.sum_nonneg fun k _ => correlationInfinite_nonneg_of_hβJ G Λ hβJ {k, j})

open IsingModel in
/-- **ℤ^d concrete instance of ∞-volume Simon-Lieb**:
for the `d`-dimensional lattice graph with cubic exhaustion,
`0 ≤ βJ`, `i ≠ j`, and `¬latticeGraph.Adj i j`:
`correlationInfinite (latticeGraph d) (cubicExhaustion d) ⟨J,0,β⟩ {i,j}
  ≤ βJ · ∑_{k~i} corrInf{k,j}`.

Direct application of `correlationInfinite_simon_lieb` to the ℤ^d setting.

Reference: Simon 1980, Comm. Math. Phys. 77, 111–126; Lieb 1980, Comm. Math.
Phys. 77, 127–135. -/
theorem correlationInfinite_simon_lieb_latticeGraph
    {d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J)
    {i j : Fin d → ℤ} (hij : i ≠ j) (hnadj : ¬(latticeGraph d).Adj i j) :
    correlationInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ {i, j}
      ≤ β * J *
          ∑ k ∈ (latticeGraph d).neighborFinset i,
            correlationInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ {k, j} :=
  correlationInfinite_simon_lieb (latticeGraph d) (cubicExhaustion d) hβJ hij hnadj

end IsingModel.Ambient
