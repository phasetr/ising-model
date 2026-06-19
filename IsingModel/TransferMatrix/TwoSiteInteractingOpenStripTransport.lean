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

end TransferMatrix

end IsingModel
