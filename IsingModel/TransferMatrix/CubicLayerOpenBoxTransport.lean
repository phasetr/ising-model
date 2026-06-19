import IsingModel.TransferMatrix.LayerOpenFiniteTransverseHermitian
import IsingModel.TransferMatrix.TwoSiteInteractingOpenStripTransport

/-!
# Cubic transverse open slab as an ambient lattice box

This file identifies the interacting cubic open slab graph
`cubicLayerOpenSlabGraph d R n`
(`= layerOpenSlabGraph (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) n`)
with the induced finite volume of the ambient lattice graph `latticeGraph (d+1)`
on a longitudinal box `cubicLayerOpenBox d R n` in `Fin (d+1) → ℤ` (longitudinal
coordinate `0 ≤ z 0 ≤ n` in coordinate `0`, transverse cube `[-R,R]^d` in
coordinates `1..d`).

Unlike the free-layer transport of `FreeLayerWalshOpenInfiniteVolume`, the cubic
transverse layer carries genuine transverse nearest-neighbour edges
(`cubicLayerGraph d R = inducedGraph (latticeGraph d) (cubicBox d R)`), so the
ambient graph is the full nearest-neighbour `latticeGraph (d+1)` — both the
longitudinal rung edges *and* the transverse lattice edges.  This generalizes the
`Fin 2` two-row strip transport of `TwoSiteInteractingOpenStripTransport` to an
arbitrary transverse cube of any dimension `d` and radius `R`.

The accompanying internal/transition/adjacency edge lemmas are stated for an
arbitrary finite transverse layer `(S, H)` with identity longitudinal transition,
so they are reusable beyond the cubic case.

The results are finite graph identifications.  They do not pass to a
thermodynamic limit or prove final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

/-! ## General open-slab edge membership (arbitrary finite transverse layer) -/

variable {S : Type*} [Fintype S] [DecidableEq S]

omit [Fintype S] in
/-- Internal (transverse) edge membership for a general layer open slab: an
internal edge joins two sites in the same layer whose transverse parts are
`H`-adjacent. -/
theorem layerOpenSlab_internal_mem (H : SimpleGraph S) [Fintype H.edgeSet]
    (n : ℕ) (a b : LayerOpenSlabSite n S) :
    s(a, b) ∈ layerOpenSlabInternalEdgeFinset (S := S) H n
      ↔ a.1 = b.1 ∧ H.Adj a.2 b.2 := by
  classical
  rw [layerOpenSlabInternalEdgeFinset, Finset.mem_biUnion]
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  constructor
  · rintro ⟨i, -, hi⟩
    rw [Finset.mem_map] at hi
    obtain ⟨e, he, hmap⟩ := hi
    revert he hmap
    refine e.ind (fun x y => ?_)
    intro he hmap
    have hxy : H.Adj x y := by
      rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeFinset]; exact he
    rw [Function.Embedding.sym2Map_apply, Sym2.map_mk, Sym2.eq_iff] at hmap
    simp only [layerOpenSlabLayerEmbedding, Function.Embedding.coeFn_mk,
      Prod.mk.injEq] at hmap
    rcases hmap with ⟨⟨rfl, rfl⟩, hb1, rfl⟩ | ⟨⟨rfl, rfl⟩, hb1, rfl⟩
    · exact ⟨hb1, hxy⟩
    · exact ⟨hb1.symm, hxy.symm⟩
  · rintro ⟨h1, hadj⟩
    simp only at h1; subst h1
    refine ⟨a1, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_map]
    refine ⟨s(a2, b2), ?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hadj
    · rw [Function.Embedding.sym2Map_apply, Sym2.map_mk]
      simp [layerOpenSlabLayerEmbedding]

/-- Transition (longitudinal) edge membership for an open slab with identity
longitudinal transition: a transition edge joins consecutive layers at the same
transverse site. -/
theorem layerOpenSlab_identityTransition_mem (n : ℕ)
    (a b : LayerOpenSlabSite n S) :
    s(a, b) ∈ layerOpenSlabTransitionEdgeFinset (S := S)
        (layerIdentityTransitionPairs S) n
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

/-- Adjacency in a general open slab graph with identity longitudinal transition:
a transverse `H`-edge (same layer) or a longitudinal nearest-neighbour step (same
transverse site). -/
theorem layerOpenSlabIdentityGraph_adj_iff (H : SimpleGraph S) [Fintype H.edgeSet]
    (n : ℕ) (a b : LayerOpenSlabSite n S) :
    (layerOpenSlabGraph (S := S) H (layerIdentityTransitionPairs S) n).Adj a b
      ↔ (a.1 = b.1 ∧ H.Adj a.2 b.2) ∨ (((a.1 : ℤ) - b.1).natAbs = 1 ∧ a.2 = b.2) := by
  classical
  rw [layerOpenSlabGraph, SimpleGraph.fromEdgeSet_adj]
  change s(a, b) ∈ layerOpenSlabEdgeFinset (S := S) H
        (layerIdentityTransitionPairs S) n ∧ a ≠ b ↔ _
  rw [layerOpenSlabEdgeFinset, Finset.mem_union, layerOpenSlab_internal_mem,
    layerOpenSlab_identityTransition_mem]
  constructor
  · rintro ⟨h, _⟩; exact h
  · intro h
    refine ⟨h, ?_⟩
    rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · intro hab; rw [hab] at h2; exact h2.ne rfl
    · intro hab; rw [hab] at h1; simp at h1

/-! ## The cubic open box and its equivalence to the cubic open slab -/

/-- The finite longitudinal box `{z : Fin (d+1) → ℤ | 0 ≤ z 0 ≤ n ∧ z (1..d) ∈
[-R,R]}`, i.e. one open longitudinal axis of length `n` over the transverse cube
`cubicBox d R`. -/
noncomputable def cubicLayerOpenBox (d R n : ℕ) : Finset (Fin (d + 1) → ℤ) :=
  Fintype.piFinset (Fin.cons (Finset.Icc (0 : ℤ) n)
    (fun _ : Fin d => Finset.Icc (-(R : ℤ)) R))

/-- Membership in the cubic open box. -/
theorem mem_cubicLayerOpenBox {d R n : ℕ} {z : Fin (d + 1) → ℤ} :
    z ∈ cubicLayerOpenBox d R n ↔
      (0 ≤ z 0 ∧ z 0 ≤ n) ∧ ∀ j : Fin d, -(R : ℤ) ≤ z j.succ ∧ z j.succ ≤ R := by
  rw [cubicLayerOpenBox, Fintype.mem_piFinset]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 := h 0; rw [Fin.cons_zero, Finset.mem_Icc] at h0; exact h0
    · intro j
      have hj := h j.succ; rw [Fin.cons_succ, Finset.mem_Icc] at hj; exact hj
  · rintro ⟨h0, hj⟩ i
    refine Fin.cases ?_ ?_ i
    · rw [Fin.cons_zero, Finset.mem_Icc]; exact h0
    · intro j; rw [Fin.cons_succ, Finset.mem_Icc]; exact hj j

/-- The cubic box point of a cubic open-slab site: longitudinal layer index in
coordinate `0`, transverse cube coordinates in `1..d`. -/
def cubicLayerOpenBoxPoint (d R n : ℕ)
    (ix : LayerOpenSlabSite n (CubicLayerSite d R)) : Fin (d + 1) → ℤ :=
  Fin.cons (ix.1.val : ℤ) (ix.2.val)

/-- The cubic box point lies in the cubic open box. -/
theorem cubicLayerOpenBoxPoint_mem (d R n : ℕ)
    (ix : LayerOpenSlabSite n (CubicLayerSite d R)) :
    cubicLayerOpenBoxPoint d R n ix ∈ cubicLayerOpenBox d R n := by
  rw [mem_cubicLayerOpenBox, cubicLayerOpenBoxPoint]
  have h1 := ix.1.isLt
  have hmem := Ambient.mem_cubicBox.mp ix.2.2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Fin.cons_zero]; positivity
  · rw [Fin.cons_zero]; omega
  · intro j; rw [Fin.cons_succ]; exact hmem j

/-- The cubic open slab over the cube `[-R,R]^d` is equivalent to the cubic open
box. -/
def cubicLayerOpenBoxEquiv (d R n : ℕ) :
    LayerOpenSlabSite n (CubicLayerSite d R) ≃ ↑(cubicLayerOpenBox d R n) where
  toFun ix := ⟨cubicLayerOpenBoxPoint d R n ix, cubicLayerOpenBoxPoint_mem d R n ix⟩
  invFun z :=
    (⟨(z.val 0).toNat, by
        have h := (mem_cubicLayerOpenBox.mp z.2).1; omega⟩,
      ⟨fun j => z.val j.succ, by
        rw [Ambient.mem_cubicBox]
        intro j; exact (mem_cubicLayerOpenBox.mp z.2).2 j⟩)
  left_inv ix := by
    obtain ⟨i, x⟩ := ix
    apply Prod.ext
    · apply Fin.ext
      simp only [cubicLayerOpenBoxPoint, Fin.cons_zero]
      have h1 := i.isLt; omega
    · apply Subtype.ext
      funext j
      simp only [cubicLayerOpenBoxPoint, Fin.cons_succ]
  right_inv z := by
    apply Subtype.ext
    funext k
    have h := mem_cubicLayerOpenBox.mp z.2
    refine Fin.cases ?_ ?_ k
    · simp only [cubicLayerOpenBoxPoint, Fin.cons_zero]
      have h0 := h.1; omega
    · intro j; simp only [cubicLayerOpenBoxPoint, Fin.cons_succ]

/-- Evaluation of the cubic box equivalence. -/
@[simp]
theorem cubicLayerOpenBoxEquiv_apply_val (d R n : ℕ)
    (ix : LayerOpenSlabSite n (CubicLayerSite d R)) :
    (cubicLayerOpenBoxEquiv d R n ix).val = cubicLayerOpenBoxPoint d R n ix := rfl

/-! ## Ambient lattice adjacency of box points -/

/-- Adjacency of cubic box points in the ambient `latticeGraph (d+1)` matches the
cubic open-slab adjacency: a transverse cube edge (same layer) or a longitudinal
nearest-neighbour step (same transverse site). -/
theorem latticeGraph_cubicLayerOpenBox_adj_iff (d R n : ℕ)
    (a b : LayerOpenSlabSite n (CubicLayerSite d R)) :
    (latticeGraph (d + 1)).Adj
        (cubicLayerOpenBoxPoint d R n a) (cubicLayerOpenBoxPoint d R n b)
      ↔ (a.1 = b.1 ∧ (cubicLayerGraph d R).Adj a.2 b.2) ∨
          (((a.1 : ℤ) - b.1).natAbs = 1 ∧ a.2 = b.2) := by
  have hL :
      (∑ i : Fin (d + 1),
          |cubicLayerOpenBoxPoint d R n a i - cubicLayerOpenBoxPoint d R n b i|)
        = |(a.1 : ℤ) - b.1| + ∑ j : Fin d, |a.2.val j - b.2.val j| := by
    rw [Fin.sum_univ_succ]
    simp only [cubicLayerOpenBoxPoint, Fin.cons_zero, Fin.cons_succ]
  -- The transverse cube edge unfolds to a `latticeGraph d` adjacency on values.
  have hAdj2 :
      (cubicLayerGraph d R).Adj a.2 b.2
        ↔ (∑ j : Fin d, |a.2.val j - b.2.val j|) = 1 := by
    rw [cubicLayerGraph, Ambient.inducedGraph_apply, SimpleGraph.induce_adj]
    change (∑ j : Fin d, |a.2.val j - b.2.val j|) = 1 ↔ _
    rfl
  have hEq2 : a.2 = b.2 ↔ (∑ j : Fin d, |a.2.val j - b.2.val j|) = 0 := by
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg _)]
    constructor
    · intro h j _; rw [h]; simp
    · intro h; apply Subtype.ext; funext j
      have := h j (Finset.mem_univ j)
      rwa [abs_eq_zero, sub_eq_zero] at this
  have hLong : ((a.1 : ℤ) - b.1).natAbs = 1 ↔ |(a.1 : ℤ) - b.1| = 1 := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast Iff.rfl
  rw [latticeGraph]
  change (∑ i : Fin (d + 1),
      |cubicLayerOpenBoxPoint d R n a i - cubicLayerOpenBoxPoint d R n b i|) = 1 ↔ _
  rw [hL, hAdj2, hEq2, hLong]
  set L : ℤ := |(a.1 : ℤ) - b.1| with hLdef
  set T : ℤ := ∑ j : Fin d, |a.2.val j - b.2.val j| with hTdef
  have hL0 : 0 ≤ L := abs_nonneg _
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hLval : (a.1 = b.1) ↔ L = 0 := by
    rw [hLdef, abs_eq_zero, sub_eq_zero]
    constructor
    · intro h; rw [h]
    · intro h; exact Fin.ext (by exact_mod_cast h)
  rw [hLval]
  constructor
  · intro h
    rcases (by omega : (L = 0 ∧ T = 1) ∨ (L = 1 ∧ T = 0)) with ⟨hl, ht⟩ | ⟨hl, ht⟩
    · exact Or.inl ⟨hl, ht⟩
    · exact Or.inr ⟨hl, ht⟩
  · rintro (⟨hl, ht⟩ | ⟨hl, ht⟩) <;> omega

/-- The cubic open slab, transported by `cubicLayerOpenBoxEquiv`, is the induced
finite volume of the ambient `latticeGraph (d+1)` on the cubic open box. -/
theorem cubicLayerOpenSlabGraph_map_boxEquiv (d R n : ℕ) :
    (cubicLayerOpenSlabGraph d R n).map (cubicLayerOpenBoxEquiv d R n).toEmbedding =
      Ambient.inducedGraph (latticeGraph (d + 1)) (cubicLayerOpenBox d R n) := by
  ext u v
  rw [SimpleGraph.map_adj, Ambient.inducedGraph_apply, SimpleGraph.induce_adj]
  constructor
  · rintro ⟨a, b, hab, hu, hv⟩
    have hslab :
        (a.1 = b.1 ∧ (cubicLayerGraph d R).Adj a.2 b.2) ∨
          (((a.1 : ℤ) - b.1).natAbs = 1 ∧ a.2 = b.2) := by
      rw [cubicLayerOpenSlabGraph] at hab
      exact (layerOpenSlabIdentityGraph_adj_iff (cubicLayerGraph d R) n a b).mp hab
    have hlat : (latticeGraph (d + 1)).Adj
        (cubicLayerOpenBoxPoint d R n a) (cubicLayerOpenBoxPoint d R n b) :=
      (latticeGraph_cubicLayerOpenBox_adj_iff d R n a b).mpr hslab
    have hua : cubicLayerOpenBoxPoint d R n a = u.val := congrArg Subtype.val hu
    have hvb : cubicLayerOpenBoxPoint d R n b = v.val := congrArg Subtype.val hv
    rwa [hua, hvb] at hlat
  · intro huv
    refine ⟨(cubicLayerOpenBoxEquiv d R n).symm u,
      (cubicLayerOpenBoxEquiv d R n).symm v, ?_, ?_, ?_⟩
    · rw [cubicLayerOpenSlabGraph]
      apply (layerOpenSlabIdentityGraph_adj_iff (cubicLayerGraph d R) n _ _).mpr
      apply (latticeGraph_cubicLayerOpenBox_adj_iff d R n _ _).mp
      have hu' :
          cubicLayerOpenBoxPoint d R n ((cubicLayerOpenBoxEquiv d R n).symm u) = u.val :=
        congrArg Subtype.val ((cubicLayerOpenBoxEquiv d R n).apply_symm_apply u)
      have hv' :
          cubicLayerOpenBoxPoint d R n ((cubicLayerOpenBoxEquiv d R n).symm v) = v.val :=
        congrArg Subtype.val ((cubicLayerOpenBoxEquiv d R n).apply_symm_apply v)
      rwa [hu', hv']
    · simp
    · simp

/-! ## Correlation transport -/

/-- Correlations on the induced finite volume of the ambient `latticeGraph (d+1)`
cubic box equal the corresponding finite cubic open-slab correlations, after
transporting the observable by `cubicLayerOpenBoxEquiv`. -/
theorem correlation_induced_latticeGraph_cubicLayerOpenBox_eq_openSlab
    (d R n : ℕ) (p : IsingParams ℝ)
    (A : Finset (LayerOpenSlabSite n (CubicLayerSite d R))) :
    correlation
        (Ambient.inducedGraph (latticeGraph (d + 1)) (cubicLayerOpenBox d R n)) p
        (A.map (cubicLayerOpenBoxEquiv d R n).toEmbedding)
      =
    correlation (cubicLayerOpenSlabGraph d R n) p A := by
  let Gopen : SimpleGraph (LayerOpenSlabSite n (CubicLayerSite d R)) :=
    cubicLayerOpenSlabGraph d R n
  let e := cubicLayerOpenBoxEquiv d R n
  calc
    correlation
        (Ambient.inducedGraph (latticeGraph (d + 1)) (cubicLayerOpenBox d R n)) p
        (A.map e.toEmbedding)
        = correlation (Gopen.map e.toEmbedding) p (A.map e.toEmbedding) :=
          correlation_congr_of_eq (cubicLayerOpenSlabGraph_map_boxEquiv d R n).symm p
            (A.map e.toEmbedding)
    _ = correlation Gopen p A := correlation_map_equiv e Gopen p A

/-- Absolute-value transport form. -/
theorem abs_correlation_induced_latticeGraph_cubicLayerOpenBox_eq_openSlab
    (d R n : ℕ) (p : IsingParams ℝ)
    (A : Finset (LayerOpenSlabSite n (CubicLayerSite d R))) :
    |correlation
        (Ambient.inducedGraph (latticeGraph (d + 1)) (cubicLayerOpenBox d R n)) p
        (A.map (cubicLayerOpenBoxEquiv d R n).toEmbedding)|
      =
    |correlation (cubicLayerOpenSlabGraph d R n) p A| := by
  rw [correlation_induced_latticeGraph_cubicLayerOpenBox_eq_openSlab]

/-! ## Transported decay on the ambient cubic box -/

/-- The generic Hermitian spectral data for the cubic transverse layer, with the
transition-weight symmetry discharged by `cubicLayerTransitionWeight_symm`. -/
noncomputable abbrev cubicLayerHermitianData (d R : ℕ) (p : IsingParams ℝ) :=
  finiteTransverseHermitianData (cubicLayerGraph d R)
    (cubicLayerTransitionPairs d R) p (cubicLayerTransitionWeight_symm d R p)

/-- The canonical maximal-index subdominant ratio for the cubic transverse
layer, with the transition-weight symmetry discharged. -/
noncomputable abbrev cubicLayerHermitianRatio (d R : ℕ) (p : IsingParams ℝ) :=
  finiteTransverseHermitianRatio (cubicLayerGraph d R)
    (cubicLayerTransitionPairs d R) p (cubicLayerTransitionWeight_symm d R p)

/-- The transported cubic same-transverse-site two-point observable on the
ambient box. -/
noncomputable def cubicLayerOpenBoxTwoPoint (d R : ℕ) (x : CubicLayerSite d R)
    (left sep right : ℕ) : Finset ↑(cubicLayerOpenBox d R (left + sep + right)) :=
  ({Prod.mk (layerOpenLeftIndex left sep right) x,
      Prod.mk (layerOpenRightIndex left sep right) x} :
        Finset (LayerOpenSlabSite (left + sep + right) (CubicLayerSite d R))).map
    (cubicLayerOpenBoxEquiv d R (left + sep + right)).toEmbedding

/-- **Finite cubic open-box decay on the ambient lattice.**  The arbitrary
finite transverse layer decay of `LayerOpenFiniteTransverseHermitian`,
specialized to the cubic transverse layer and transported onto the induced
finite volume of the ambient `latticeGraph (d+1)` on the cubic open box.  The
transition-weight symmetry is discharged automatically; the only inputs are the
boundary-window gap and a columnwise-simple-eigenspace parity input, at zero
field.  This is finite: it does not pass to a thermodynamic limit or prove final
hyperplane exponential decay. -/
theorem
    correlation_induced_latticeGraph_cubicLayerOpenBox_abs_le_of_hermitianCanonicalRatioSimpleParityWindow
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0) (x : CubicLayerSite d R)
    (hwindow :
      cubicLayerHermitianRatio d R p <
        layerOpenBoundarySpectralWindowCap (layerInternalWeight (cubicLayerGraph d R) p)
          (cubicLayerHermitianData d R p) (cubicLayerHermitianData d R p).maxEigenIndex)
    (hsimple : (cubicLayerHermitianData d R p).ColumnSimpleEigenspaces)
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (Ambient.inducedGraph (latticeGraph (d + 1))
          (cubicLayerOpenBox d R (left + sep + right))) p
        (cubicLayerOpenBoxTwoPoint d R x left sep right)|
      ≤
        ((cubicLayerHermitianData d R p).boundaryMarkedSpectralPrefactor
            (layerSpinAt x)
            (layerOpenBalancedBoundaryVector (layerInternalWeight (cubicLayerGraph d R) p))
            (layerOpenBalancedBoundaryVector (layerInternalWeight (cubicLayerGraph d R) p)) /
          (cubicLayerHermitianData d R p).boundarySpectralPartitionPrefactor
            (layerOpenBalancedBoundaryVector (layerInternalWeight (cubicLayerGraph d R) p))
            (cubicLayerHermitianData d R p).maxEigenIndex (cubicLayerHermitianRatio d R p)) *
          cubicLayerHermitianRatio d R p ^ sep := by
  rw [cubicLayerOpenBoxTwoPoint,
    abs_correlation_induced_latticeGraph_cubicLayerOpenBox_eq_openSlab]
  exact correlation_cubicLayerOpenSlabGraph_abs_le_of_hermitianCanonicalRatioSimpleParityWindow
    d R p hp x (cubicLayerTransitionWeight_symm d R p) hwindow hsimple left sep right hsep

end TransferMatrix

end IsingModel
