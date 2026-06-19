import IsingModel.TransferMatrix.FreeLayerWalshOpenDecay
import IsingModel.Concrete.CubicExhaustion
import IsingModel.AmbientLatticeSum.InducedUnion

/-!
# Ambient finite-volume bridge for free-layer open Walsh decay

This file transports finite free-layer open-slab correlations to the ambient
finite-volume framework for the longitudinal-only free-layer graph.
The ambient graph has no transverse edges: only the first coordinate changes,
by one lattice step, while all transverse coordinates are fixed.  This matches
the `H = ⊥` hypothesis in the finite open-slab theorem.

The results intentionally do not assert decay for the full cubic lattice graph,
where transverse nearest-neighbour edges are present, nor for interacting
transverse layers.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

/-! ## Longitudinal-only free-layer ambient graph -/

/-- The longitudinal-only free-layer graph on `Z^(d+1)`.

Two vertices are adjacent exactly when the first coordinate differs by one and
all transverse coordinates agree.  This graph is the infinite-volume ambient
counterpart of the finite open free-layer slab with transverse graph `⊥`. -/
def freeLayerAxisGraph (d : ℕ) : SimpleGraph (Fin (d + 1) → ℤ) where
  Adj x y := (x 0 - y 0).natAbs = 1 ∧ ∀ j : Fin d, x j.succ = y j.succ
  symm := by
    intro x y h
    exact ⟨by
      rw [show y 0 - x 0 = -(x 0 - y 0) by ring, Int.natAbs_neg]
      exact h.1, fun j => (h.2 j).symm⟩
  loopless := ⟨fun x h => by
    simp at h⟩

/-- Adjacency in `freeLayerAxisGraph` is decidable. -/
instance (d : ℕ) : DecidableRel (freeLayerAxisGraph d).Adj :=
  fun x y => inferInstanceAs
    (Decidable ((x 0 - y 0).natAbs = 1 ∧ ∀ j : Fin d, x j.succ = y j.succ))

/-- The point of `Z^(d+1)` with longitudinal coordinate `t` and transverse
coordinate `x`. -/
def freeLayerAxisPoint (d : ℕ) (t : ℤ) (x : Fin d → ℤ) : Fin (d + 1) → ℤ :=
  Fin.cases t x

/-- The longitudinal coordinate of `freeLayerAxisPoint`. -/
@[simp]
theorem freeLayerAxisPoint_zero (d : ℕ) (t : ℤ) (x : Fin d → ℤ) :
    freeLayerAxisPoint d t x 0 = t := by
  rfl

/-- The transverse coordinates of `freeLayerAxisPoint`. -/
@[simp]
theorem freeLayerAxisPoint_succ (d : ℕ) (t : ℤ) (x : Fin d → ℤ) (j : Fin d) :
    freeLayerAxisPoint d t x j.succ = x j := by
  rfl

/-- A point with bounded longitudinal coordinate and bounded transverse
coordinate lies in the cubic box of the full free-layer ambient space. -/
theorem freeLayerAxisPoint_mem_cubicBox {d N : ℕ} {t : ℤ} {x : Fin d → ℤ}
    (ht : -(N : ℤ) ≤ t ∧ t ≤ N) (hx : x ∈ Ambient.cubicBox d N) :
    freeLayerAxisPoint d t x ∈ Ambient.cubicBox (d + 1) N := by
  rw [Ambient.mem_cubicBox] at hx ⊢
  intro k
  refine Fin.cases ?_ ?_ k
  · simpa using ht
  · intro j
    simpa using hx j

/-! ## Cubic-box finite slab equivalence -/

/-- Embed the finite open free-layer slab over the transverse cubic box into the
ambient cubic box, shifting the longitudinal coordinate `i` to `i - N`. -/
def freeLayerOpenSlabCubicBoxPoint (d N : ℕ)
    (ix : LayerOpenSlabSite (2 * N) (CubicLayerSite d N)) : Fin (d + 1) → ℤ :=
  freeLayerAxisPoint d ((ix.1 : ℤ) - N) ix.2.val

/-- The finite open free-layer slab point lies in the ambient cubic box. -/
theorem freeLayerOpenSlabCubicBoxPoint_mem (d N : ℕ)
    (ix : LayerOpenSlabSite (2 * N) (CubicLayerSite d N)) :
    freeLayerOpenSlabCubicBoxPoint d N ix ∈ Ambient.cubicBox (d + 1) N := by
  apply freeLayerAxisPoint_mem_cubicBox
  · have hlt := ix.1.isLt
    constructor <;> omega
  · exact ix.2.2

/-- The finite open free-layer slab over `cubicBox d N` is equivalent to the
ambient cubic box in `Z^(d+1)`. -/
def freeLayerOpenSlabCubicBoxEquiv (d N : ℕ) :
    LayerOpenSlabSite (2 * N) (CubicLayerSite d N) ≃
      ↑(Ambient.cubicBox (d + 1) N) where
  toFun ix := ⟨freeLayerOpenSlabCubicBoxPoint d N ix,
    freeLayerOpenSlabCubicBoxPoint_mem d N ix⟩
  invFun y :=
    (⟨(y.val 0 + N).toNat, by
        have hy := (Ambient.mem_cubicBox.mp y.2) 0
        omega⟩,
      ⟨fun j => y.val j.succ, by
        rw [Ambient.mem_cubicBox]
        intro j
        exact (Ambient.mem_cubicBox.mp y.2) j.succ⟩)
  left_inv ix := by
    ext
    · simp [freeLayerOpenSlabCubicBoxPoint, freeLayerAxisPoint]
    · simp [freeLayerOpenSlabCubicBoxPoint, freeLayerAxisPoint]
  right_inv y := by
    apply Subtype.ext
    funext k
    refine Fin.cases ?_ ?_ k
    · simp [freeLayerOpenSlabCubicBoxPoint, freeLayerAxisPoint]
      have hy := (Ambient.mem_cubicBox.mp y.2) 0
      omega
    · intro j
      simp [freeLayerOpenSlabCubicBoxPoint, freeLayerAxisPoint]

/-- Evaluation of the finite-slab to cubic-box equivalence. -/
@[simp]
theorem freeLayerOpenSlabCubicBoxEquiv_apply_val (d N : ℕ)
    (ix : LayerOpenSlabSite (2 * N) (CubicLayerSite d N)) :
    (freeLayerOpenSlabCubicBoxEquiv d N ix).val =
      freeLayerOpenSlabCubicBoxPoint d N ix := by
  rfl

/-- The inverse equivalence recovers the longitudinal slab index from the first
ambient coordinate. -/
@[simp]
theorem freeLayerOpenSlabCubicBoxEquiv_symm_fst (d N : ℕ)
    (y : ↑(Ambient.cubicBox (d + 1) N)) :
    ((freeLayerOpenSlabCubicBoxEquiv d N).symm y).1.val =
      (y.val 0 + N).toNat := by
  rfl

/-- The inverse equivalence recovers the transverse coordinate from the remaining
ambient coordinates. -/
@[simp]
theorem freeLayerOpenSlabCubicBoxEquiv_symm_snd_val (d N : ℕ)
    (y : ↑(Ambient.cubicBox (d + 1) N)) (j : Fin d) :
    ((freeLayerOpenSlabCubicBoxEquiv d N).symm y).2.val j = y.val j.succ := by
  rfl

/-! ## Finite graph identification -/

/-- Adjacency in the finite open free-layer slab is exactly longitudinal
nearest-neighbour adjacency with the transverse coordinate fixed. -/
theorem freeLayerOpenSlabGraph_adj_iff (d N : ℕ)
    (a b : LayerOpenSlabSite (2 * N) (CubicLayerSite d N)) :
    (layerOpenSlabGraph (S := CubicLayerSite d N)
      (⊥ : SimpleGraph (CubicLayerSite d N))
      (layerIdentityTransitionPairs (CubicLayerSite d N)) (2 * N)).Adj a b
      ↔ ((a.1 : ℤ) - b.1).natAbs = 1 ∧ a.2 = b.2 := by
  classical
  rw [layerOpenSlabGraph, SimpleGraph.fromEdgeSet_adj]
  change s(a, b) ∈ layerOpenSlabEdgeFinset (S := CubicLayerSite d N)
        (⊥ : SimpleGraph (CubicLayerSite d N))
        (layerIdentityTransitionPairs (CubicLayerSite d N)) (2 * N) ∧ a ≠ b ↔
      ((a.1 : ℤ) - b.1).natAbs = 1 ∧ a.2 = b.2
  rw [layerOpenSlabEdgeFinset, Finset.mem_union]
  have hnot_internal :
      s(a, b) ∉ layerOpenSlabInternalEdgeFinset (S := CubicLayerSite d N)
        (⊥ : SimpleGraph (CubicLayerSite d N)) (2 * N) := by
    rw [layerOpenSlabInternalEdgeFinset, Finset.mem_biUnion]
    rintro ⟨i, _hi, hmap⟩
    simp at hmap
  rw [or_iff_right hnot_internal]
  rw [layerOpenSlabTransitionEdgeFinset, Finset.mem_image]
  simp only [layerIdentityTransitionPairs, layerOpenSlabTransitionEdge, Prod.ext_iff,
    Finset.univ_eq_attach, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_univ, Finset.mem_image, Finset.mem_attach, true_and, exists_eq_left,
    Sym2.eq, Sym2.rel_iff', Prod.swap_prod_mk, Prod.exists, exists_eq_left',
    Subtype.exists, ne_eq, not_and]
  constructor
  · rintro ⟨hedge, _hne⟩
    rcases hedge with ⟨i, x, hx, hcase⟩
    rcases hcase with hcase | hcase
    · rcases hcase with ⟨⟨hia, hxa⟩, hib, hxb⟩
      constructor
      · rw [← hia, ← hib]
        simp
      · exact hxa.symm.trans hxb
    · rcases hcase with ⟨⟨hib, hxb⟩, hia, hxa⟩
      constructor
      · rw [← hia, ← hib]
        simp
      · exact hxa.symm.trans hxb
  · rintro ⟨hdist, htrans⟩
    have hor :
        a.1.val + 1 = b.1.val ∨ b.1.val + 1 = a.1.val := by
      have ha := a.1.isLt
      have hb := b.1.isLt
      omega
    constructor
    · rcases hor with hab | hba
      · refine ⟨⟨a.1.val, by omega⟩, a.2.val, a.2.2, Or.inl ?_⟩
        constructor
        · constructor
          · apply Fin.ext
            simp
          · rfl
        · constructor
          · apply Fin.ext
            simp [hab]
          · exact htrans
      · refine ⟨⟨b.1.val, by omega⟩, b.2.val, b.2.2, Or.inr ?_⟩
        constructor
        · constructor
          · apply Fin.ext
            simp
          · rfl
        · constructor
          · apply Fin.ext
            simp [hba]
          · exact htrans.symm
    · intro hsame _htrans
      have hzero : ((a.1 : ℤ) - b.1).natAbs = 0 := by
        rw [hsame]
        simp
      omega

/-- The cubic-box embedding turns finite open-slab adjacency into
longitudinal-only ambient adjacency. -/
theorem freeLayerAxisGraph_adj_point_iff (d N : ℕ)
    (a b : LayerOpenSlabSite (2 * N) (CubicLayerSite d N)) :
    (freeLayerAxisGraph d).Adj
        (freeLayerOpenSlabCubicBoxPoint d N a)
        (freeLayerOpenSlabCubicBoxPoint d N b)
      ↔ ((a.1 : ℤ) - b.1).natAbs = 1 ∧ a.2 = b.2 := by
  constructor
  · intro h
    constructor
    · simpa [freeLayerAxisGraph, freeLayerOpenSlabCubicBoxPoint,
        freeLayerAxisPoint] using h.1
    · apply Subtype.ext
      funext j
      simpa [freeLayerAxisGraph, freeLayerOpenSlabCubicBoxPoint,
        freeLayerAxisPoint] using h.2 j
  · rintro ⟨hcoord, htrans⟩
    constructor
    · simpa [freeLayerAxisGraph, freeLayerOpenSlabCubicBoxPoint,
        freeLayerAxisPoint] using hcoord
    · intro j
      simp [freeLayerOpenSlabCubicBoxPoint, freeLayerAxisPoint, htrans]

/-- The finite open free-layer slab over `cubicBox d N`, transported by
`freeLayerOpenSlabCubicBoxEquiv`, is the induced finite volume of the
longitudinal-only free-layer ambient graph. -/
theorem freeLayerOpenSlabGraph_map_cubicBoxEquiv (d N : ℕ) :
    (layerOpenSlabGraph (S := CubicLayerSite d N)
        (⊥ : SimpleGraph (CubicLayerSite d N))
        (layerIdentityTransitionPairs (CubicLayerSite d N)) (2 * N)).map
      (freeLayerOpenSlabCubicBoxEquiv d N).toEmbedding =
    Ambient.inducedGraph (freeLayerAxisGraph d) (Ambient.cubicBox (d + 1) N) := by
  ext u v
  rw [SimpleGraph.map_adj, Ambient.inducedGraph_apply, SimpleGraph.induce_adj]
  constructor
  · rintro ⟨a, b, hab, hu, hv⟩
    have haxis :
        (freeLayerAxisGraph d).Adj
          (freeLayerOpenSlabCubicBoxPoint d N a)
          (freeLayerOpenSlabCubicBoxPoint d N b) := by
      exact (freeLayerAxisGraph_adj_point_iff d N a b).mpr
        ((freeLayerOpenSlabGraph_adj_iff d N a b).mp hab)
    have hua :
        freeLayerOpenSlabCubicBoxPoint d N a = u.val := by
      simpa [freeLayerOpenSlabCubicBoxEquiv_apply_val] using congrArg Subtype.val hu
    have hvb :
        freeLayerOpenSlabCubicBoxPoint d N b = v.val := by
      simpa [freeLayerOpenSlabCubicBoxEquiv_apply_val] using congrArg Subtype.val hv
    simpa [hua, hvb] using haxis
  · intro huv
    refine ⟨(freeLayerOpenSlabCubicBoxEquiv d N).symm u,
      (freeLayerOpenSlabCubicBoxEquiv d N).symm v, ?_, ?_, ?_⟩
    · apply (freeLayerOpenSlabGraph_adj_iff d N _ _).mpr
      apply (freeLayerAxisGraph_adj_point_iff d N _ _).mp
      have hu' :
          freeLayerOpenSlabCubicBoxPoint d N
              ((freeLayerOpenSlabCubicBoxEquiv d N).symm u) = u.val := by
        exact congrArg Subtype.val
          ((freeLayerOpenSlabCubicBoxEquiv d N).apply_symm_apply u)
      have hv' :
          freeLayerOpenSlabCubicBoxPoint d N
              ((freeLayerOpenSlabCubicBoxEquiv d N).symm v) = v.val := by
        exact congrArg Subtype.val
          ((freeLayerOpenSlabCubicBoxEquiv d N).apply_symm_apply v)
      simpa [hu', hv'] using huv
    · simp
    · simp

/-! ## Finite cubic-box correlation transport -/

/-- The centre layer index in the `2N`-step open slab identified with
`[-N,N]` in the longitudinal coordinate. -/
def freeLayerOpenCubicLeftIndex (N : ℕ) : Fin (2 * N + 1) :=
  ⟨N, by omega⟩

/-- The right layer index at separation `sep` from the centre layer in the
`2N`-step open slab. -/
def freeLayerOpenCubicRightIndex (N sep : ℕ) (hsepN : sep ≤ N) : Fin (2 * N + 1) :=
  ⟨N + sep, by omega⟩

/-- Correlations on the induced finite volume of the longitudinal-only ambient
graph are the corresponding finite open free-layer slab correlations, after
transporting the observable by `freeLayerOpenSlabCubicBoxEquiv`. -/
theorem correlation_induced_freeLayerAxisGraph_cubicBox_eq_openSlab
    (d N : ℕ) (p : IsingParams ℝ)
    (A : Finset (LayerOpenSlabSite (2 * N) (CubicLayerSite d N))) :
    correlation
        (Ambient.inducedGraph (freeLayerAxisGraph d) (Ambient.cubicBox (d + 1) N)) p
        (A.map (freeLayerOpenSlabCubicBoxEquiv d N).toEmbedding)
      =
    correlation
        (layerOpenSlabGraph (S := CubicLayerSite d N)
          (⊥ : SimpleGraph (CubicLayerSite d N))
          (layerIdentityTransitionPairs (CubicLayerSite d N)) (2 * N)) p A := by
  let Gopen : SimpleGraph (LayerOpenSlabSite (2 * N) (CubicLayerSite d N)) :=
    layerOpenSlabGraph (S := CubicLayerSite d N)
      (⊥ : SimpleGraph (CubicLayerSite d N))
      (layerIdentityTransitionPairs (CubicLayerSite d N)) (2 * N)
  let e := freeLayerOpenSlabCubicBoxEquiv d N
  calc
    correlation
        (Ambient.inducedGraph (freeLayerAxisGraph d) (Ambient.cubicBox (d + 1) N)) p
        (A.map e.toEmbedding)
        = correlation (Gopen.map e.toEmbedding) p (A.map e.toEmbedding) := by
            exact correlation_congr_of_eq
              (freeLayerOpenSlabGraph_map_cubicBoxEquiv d N).symm p
              (A.map e.toEmbedding)
    _ = correlation Gopen p A := by
            exact correlation_map_equiv e Gopen p A

/-- Absolute-value transport form of
`correlation_induced_freeLayerAxisGraph_cubicBox_eq_openSlab`. -/
theorem abs_correlation_induced_freeLayerAxisGraph_cubicBox_eq_openSlab
    (d N : ℕ) (p : IsingParams ℝ)
    (A : Finset (LayerOpenSlabSite (2 * N) (CubicLayerSite d N))) :
    |correlation
        (Ambient.inducedGraph (freeLayerAxisGraph d) (Ambient.cubicBox (d + 1) N)) p
        (A.map (freeLayerOpenSlabCubicBoxEquiv d N).toEmbedding)|
      =
    |correlation
        (layerOpenSlabGraph (S := CubicLayerSite d N)
          (⊥ : SimpleGraph (CubicLayerSite d N))
          (layerIdentityTransitionPairs (CubicLayerSite d N)) (2 * N)) p A| := by
  rw [correlation_induced_freeLayerAxisGraph_cubicBox_eq_openSlab]

/-- A finite open-slab correlation bound transports to the induced finite volume
of the longitudinal-only ambient graph. -/
theorem abs_correlation_induced_freeLayerAxisGraph_cubicBox_le_of_openSlab
    (d N : ℕ) (p : IsingParams ℝ)
    (A : Finset (LayerOpenSlabSite (2 * N) (CubicLayerSite d N))) {C : ℝ}
    (hA :
      |correlation
        (layerOpenSlabGraph (S := CubicLayerSite d N)
          (⊥ : SimpleGraph (CubicLayerSite d N))
          (layerIdentityTransitionPairs (CubicLayerSite d N)) (2 * N)) p A| ≤ C) :
    |correlation
        (Ambient.inducedGraph (freeLayerAxisGraph d) (Ambient.cubicBox (d + 1) N)) p
        (A.map (freeLayerOpenSlabCubicBoxEquiv d N).toEmbedding)|
      ≤ C := by
  rw [abs_correlation_induced_freeLayerAxisGraph_cubicBox_eq_openSlab]
  exact hA

end TransferMatrix

end IsingModel
