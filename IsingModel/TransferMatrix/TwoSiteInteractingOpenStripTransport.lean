import IsingModel.TransferMatrix.FreeLayerWalshOpenInfiniteVolume

/-!
# Two-site interacting open slab as a lattice strip

This file identifies the interacting `K2` open slab graph
`layerOpenSlabGraph (completeGraph (Fin 2)) (layerIdentityTransitionPairs (Fin 2)) n`
with the induced finite volume of the ambient lattice graph `latticeGraph 2` on
a two-row strip `twoSiteOpenStrip n` in `Fin 2 → ℤ` (longitudinal coordinate
`0 ≤ z 0 ≤ n`, transverse rung `0 ≤ z 1 ≤ 1`).  Unlike the free-layer transport
of `FreeLayerWalshOpenInfiniteVolume`, the interacting layer has a transverse
edge, so the ambient graph is the full nearest-neighbour `latticeGraph 2`
(longitudinal edges *and* the transverse rung), not a longitudinal-only axis
graph.  The correlation transport lemma carries finite interacting open-slab
bounds into the project's induced lattice-graph correlation form.

The results are finite graph identifications.  They do not pass to a
thermodynamic limit or prove final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

/-! ## The two-row open strip and its equivalence to the layer open slab -/

/-- The finite two-row strip `{z : Fin 2 → ℤ | 0 ≤ z 0 ≤ n ∧ 0 ≤ z 1 ≤ 1}`. -/
noncomputable def twoSiteOpenStrip (n : ℕ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset ![Finset.Icc (0 : ℤ) n, Finset.Icc (0 : ℤ) 1]

/-- Membership in the two-row open strip. -/
theorem mem_twoSiteOpenStrip {n : ℕ} {z : Fin 2 → ℤ} :
    z ∈ twoSiteOpenStrip n ↔ 0 ≤ z 0 ∧ z 0 ≤ n ∧ 0 ≤ z 1 ∧ z 1 ≤ 1 := by
  rw [twoSiteOpenStrip, Fintype.mem_piFinset, Fin.forall_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mem_Icc]
  tauto

/-- The strip point of a layer open-slab site: longitudinal layer index in
coordinate `0`, transverse site in coordinate `1`. -/
def twoSiteOpenStripPoint (n : ℕ) (ix : LayerOpenSlabSite n (Fin 2)) : Fin 2 → ℤ :=
  ![(ix.1.val : ℤ), (ix.2.val : ℤ)]

/-- The strip point lies in the two-row strip. -/
theorem twoSiteOpenStripPoint_mem (n : ℕ) (ix : LayerOpenSlabSite n (Fin 2)) :
    twoSiteOpenStripPoint n ix ∈ twoSiteOpenStrip n := by
  rw [mem_twoSiteOpenStrip, twoSiteOpenStripPoint]
  have h1 := ix.1.isLt; have h2 := ix.2.isLt
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨by positivity, by omega, by positivity, by omega⟩

/-- The layer open slab over `Fin 2` is equivalent to the two-row strip. -/
def twoSiteOpenStripEquiv (n : ℕ) :
    LayerOpenSlabSite n (Fin 2) ≃ ↑(twoSiteOpenStrip n) where
  toFun ix := ⟨twoSiteOpenStripPoint n ix, twoSiteOpenStripPoint_mem n ix⟩
  invFun y :=
    (⟨(y.val 0).toNat, by have h := mem_twoSiteOpenStrip.mp y.2; omega⟩,
      ⟨(y.val 1).toNat, by have h := mem_twoSiteOpenStrip.mp y.2; omega⟩)
  left_inv ix := by
    ext
    · simp [twoSiteOpenStripPoint]
    · simp [twoSiteOpenStripPoint]
  right_inv y := by
    apply Subtype.ext
    funext k
    have h := mem_twoSiteOpenStrip.mp y.2
    fin_cases k <;> simp [twoSiteOpenStripPoint] <;> omega

/-- Evaluation of the strip equivalence. -/
@[simp]
theorem twoSiteOpenStripEquiv_apply_val (n : ℕ) (ix : LayerOpenSlabSite n (Fin 2)) :
    (twoSiteOpenStripEquiv n ix).val = twoSiteOpenStripPoint n ix := rfl

/-! ## Finite graph identification -/

/-- The internal (transverse rung) edge membership for the `K2` open slab. -/
theorem twoSiteOpenSlab_internal_mem (n : ℕ) (a b : LayerOpenSlabSite n (Fin 2)) :
    s(a, b) ∈ layerOpenSlabInternalEdgeFinset (SimpleGraph.completeGraph (Fin 2)) n
      ↔ a.1 = b.1 ∧ a.2 ≠ b.2 := by
  classical
  rw [layerOpenSlabInternalEdgeFinset, Finset.mem_biUnion,
    show ((SimpleGraph.completeGraph (Fin 2)).edgeFinset) = {s(0, 1)} from by decide]
  simp only [Finset.mem_univ, true_and, Finset.map_singleton, Finset.mem_singleton,
    Function.Embedding.sym2Map_apply, Sym2.map_mk, layerOpenSlabLayerEmbedding,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨i, hi⟩
    rw [Sym2.eq_iff] at hi
    rcases hi with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      (subst ha; subst hb; exact ⟨rfl, by simp⟩)
  · rintro ⟨h1, h2⟩
    refine ⟨a.1, ?_⟩
    rw [Sym2.eq_iff]
    obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
    simp only at h1 h2
    subst h1
    fin_cases a2 <;> fin_cases b2 <;> simp_all

/-- The transition (longitudinal nearest-neighbour) edge membership for the `K2`
open slab with identity longitudinal transition. -/
theorem twoSiteOpenSlab_transition_mem (n : ℕ) (a b : LayerOpenSlabSite n (Fin 2)) :
    s(a, b) ∈ layerOpenSlabTransitionEdgeFinset (S := Fin 2)
        (layerIdentityTransitionPairs (Fin 2)) n
      ↔ ((a.1 : ℤ) - b.1).natAbs = 1 ∧ a.2 = b.2 := by
  classical
  rw [layerOpenSlabTransitionEdgeFinset, Finset.mem_image]
  simp only [layerIdentityTransitionPairs, layerOpenSlabTransitionEdge, Prod.ext_iff,
    Finset.product_eq_sprod, Finset.mem_product, Finset.mem_univ, Finset.mem_image,
    true_and, exists_eq_left, Sym2.eq, Sym2.rel_iff',
    Prod.swap_prod_mk, Prod.exists, exists_eq_left']
  constructor
  · rintro ⟨i, x, hc⟩
    rcases hc with ⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩
    · refine ⟨?_, h2.symm.trans h4⟩
      rw [← h1, ← h3]; simp only [Fin.val_castSucc, Fin.val_succ]; push_cast; omega
    · refine ⟨?_, h4.symm.trans h2⟩
      rw [← h1, ← h3]; simp only [Fin.val_castSucc, Fin.val_succ]; push_cast; omega
  · rintro ⟨hdist, htrans⟩
    have hor : a.1.val + 1 = b.1.val ∨ b.1.val + 1 = a.1.val := by
      have ha := a.1.isLt; have hb := b.1.isLt; omega
    rcases hor with hab | hba
    · refine ⟨⟨a.1.val, by omega⟩, a.2, Or.inl ⟨⟨?_, rfl⟩, ?_, htrans⟩⟩
      · apply Fin.ext; simp
      · apply Fin.ext; simp [hab]
    · refine ⟨⟨b.1.val, by omega⟩, b.2, Or.inr ⟨⟨?_, rfl⟩, ?_, htrans.symm⟩⟩
      · apply Fin.ext; simp
      · apply Fin.ext; simp [hba]

/-- Adjacency in the `K2` open slab graph: a transverse rung (same layer,
distinct transverse sites) or a longitudinal nearest-neighbour step (consecutive
layers, same transverse site). -/
theorem twoSiteOpenSlabGraph_adj_iff (n : ℕ) (a b : LayerOpenSlabSite n (Fin 2)) :
    (layerOpenSlabGraph (S := Fin 2) (SimpleGraph.completeGraph (Fin 2))
        (layerIdentityTransitionPairs (Fin 2)) n).Adj a b
      ↔ (a.1 = b.1 ∧ a.2 ≠ b.2) ∨ (((a.1 : ℤ) - b.1).natAbs = 1 ∧ a.2 = b.2) := by
  classical
  rw [layerOpenSlabGraph, SimpleGraph.fromEdgeSet_adj]
  change s(a, b) ∈ layerOpenSlabEdgeFinset (S := Fin 2)
        (SimpleGraph.completeGraph (Fin 2))
        (layerIdentityTransitionPairs (Fin 2)) n ∧ a ≠ b ↔ _
  rw [layerOpenSlabEdgeFinset, Finset.mem_union, twoSiteOpenSlab_internal_mem,
    twoSiteOpenSlab_transition_mem]
  constructor
  · rintro ⟨h, _⟩; exact h
  · intro h
    refine ⟨h, ?_⟩
    rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · intro hab; exact h2 (congrArg Prod.snd hab)
    · intro hab; rw [hab] at h1; simp at h1

/-- Adjacency of strip points in the ambient `latticeGraph 2` matches the `K2`
open-slab adjacency. -/
theorem latticeGraph_two_strip_adj_iff (n : ℕ) (a b : LayerOpenSlabSite n (Fin 2)) :
    (latticeGraph 2).Adj (twoSiteOpenStripPoint n a) (twoSiteOpenStripPoint n b)
      ↔ (a.1 = b.1 ∧ a.2 ≠ b.2) ∨ (((a.1 : ℤ) - b.1).natAbs = 1 ∧ a.2 = b.2) := by
  rw [latticeGraph, twoSiteOpenStripPoint, twoSiteOpenStripPoint]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [ne_eq]
  constructor
  · intro h
    by_cases hc : a2 = b2
    · subst hc
      refine Or.inr ⟨?_, rfl⟩
      simp only [sub_self, abs_zero, add_zero] at h
      rw [Int.abs_eq_natAbs] at h
      exact_mod_cast h
    · refine Or.inl ⟨?_, hc⟩
      have ha2 := a2.isLt; have hb2 := b2.isLt
      have : (a2 : ℤ) ≠ (b2 : ℤ) := by
        simpa [Fin.val_inj] using hc
      have hd : |(a2 : ℤ) - (b2 : ℤ)| = 1 := by
        interval_cases h2a : a2.val <;> interval_cases h2b : b2.val <;> simp_all
      rw [hd] at h
      have : |(a1 : ℤ) - (b1 : ℤ)| = 0 := by omega
      have : (a1 : ℤ) = (b1 : ℤ) := by rwa [abs_eq_zero, sub_eq_zero] at this
      exact Fin.ext (by exact_mod_cast this)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · subst h1
      have : |(a2 : ℤ) - (b2 : ℤ)| = 1 := by
        have ha2 := a2.isLt; have hb2 := b2.isLt
        have : (a2 : ℤ) ≠ (b2 : ℤ) := by simpa [Fin.val_inj] using h2
        interval_cases h2a : a2.val <;> interval_cases h2b : b2.val <;> simp_all
      simp only [sub_self, abs_zero, zero_add, this]
    · subst h2
      simp only [sub_self, abs_zero, add_zero]
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h1

/-- The `K2` open slab, transported by `twoSiteOpenStripEquiv`, is the induced
finite volume of the ambient `latticeGraph 2` on the two-row strip. -/
theorem twoSiteOpenSlabGraph_map_stripEquiv (n : ℕ) :
    (layerOpenSlabGraph (S := Fin 2) (SimpleGraph.completeGraph (Fin 2))
        (layerIdentityTransitionPairs (Fin 2)) n).map
      (twoSiteOpenStripEquiv n).toEmbedding =
    Ambient.inducedGraph (latticeGraph 2) (twoSiteOpenStrip n) := by
  ext u v
  rw [SimpleGraph.map_adj, Ambient.inducedGraph_apply, SimpleGraph.induce_adj]
  constructor
  · rintro ⟨a, b, hab, hu, hv⟩
    have hlat : (latticeGraph 2).Adj
        (twoSiteOpenStripPoint n a) (twoSiteOpenStripPoint n b) :=
      (latticeGraph_two_strip_adj_iff n a b).mpr
        ((twoSiteOpenSlabGraph_adj_iff n a b).mp hab)
    have hua : twoSiteOpenStripPoint n a = u.val :=
      congrArg Subtype.val hu
    have hvb : twoSiteOpenStripPoint n b = v.val :=
      congrArg Subtype.val hv
    rwa [hua, hvb] at hlat
  · intro huv
    refine ⟨(twoSiteOpenStripEquiv n).symm u, (twoSiteOpenStripEquiv n).symm v, ?_, ?_, ?_⟩
    · apply (twoSiteOpenSlabGraph_adj_iff n _ _).mpr
      apply (latticeGraph_two_strip_adj_iff n _ _).mp
      have hu' : twoSiteOpenStripPoint n ((twoSiteOpenStripEquiv n).symm u) = u.val :=
        congrArg Subtype.val ((twoSiteOpenStripEquiv n).apply_symm_apply u)
      have hv' : twoSiteOpenStripPoint n ((twoSiteOpenStripEquiv n).symm v) = v.val :=
        congrArg Subtype.val ((twoSiteOpenStripEquiv n).apply_symm_apply v)
      rwa [hu', hv']
    · simp
    · simp

/-! ## Correlation transport -/

/-- Correlations on the induced finite volume of the ambient `latticeGraph 2`
strip equal the corresponding finite `K2` open-slab correlations, after
transporting the observable by `twoSiteOpenStripEquiv`. -/
theorem correlation_induced_latticeGraph_two_strip_eq_openSlab
    (n : ℕ) (p : IsingParams ℝ)
    (A : Finset (LayerOpenSlabSite n (Fin 2))) :
    correlation (Ambient.inducedGraph (latticeGraph 2) (twoSiteOpenStrip n)) p
        (A.map (twoSiteOpenStripEquiv n).toEmbedding)
      =
    correlation (layerOpenSlabGraph (S := Fin 2) (SimpleGraph.completeGraph (Fin 2))
      (layerIdentityTransitionPairs (Fin 2)) n) p A := by
  let Gopen : SimpleGraph (LayerOpenSlabSite n (Fin 2)) :=
    layerOpenSlabGraph (S := Fin 2) (SimpleGraph.completeGraph (Fin 2))
      (layerIdentityTransitionPairs (Fin 2)) n
  let e := twoSiteOpenStripEquiv n
  calc
    correlation (Ambient.inducedGraph (latticeGraph 2) (twoSiteOpenStrip n)) p
        (A.map e.toEmbedding)
        = correlation (Gopen.map e.toEmbedding) p (A.map e.toEmbedding) :=
          correlation_congr_of_eq (twoSiteOpenSlabGraph_map_stripEquiv n).symm p
            (A.map e.toEmbedding)
    _ = correlation Gopen p A := correlation_map_equiv e Gopen p A

/-- Absolute-value transport form. -/
theorem abs_correlation_induced_latticeGraph_two_strip_eq_openSlab
    (n : ℕ) (p : IsingParams ℝ)
    (A : Finset (LayerOpenSlabSite n (Fin 2))) :
    |correlation (Ambient.inducedGraph (latticeGraph 2) (twoSiteOpenStrip n)) p
        (A.map (twoSiteOpenStripEquiv n).toEmbedding)|
      =
    |correlation (layerOpenSlabGraph (S := Fin 2) (SimpleGraph.completeGraph (Fin 2))
      (layerIdentityTransitionPairs (Fin 2)) n) p A| := by
  rw [correlation_induced_latticeGraph_two_strip_eq_openSlab]

end TransferMatrix

end IsingModel
