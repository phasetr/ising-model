import IsingModel.TransferMatrix.FreeLayerWalshOpenInfiniteVolume

/-!
# Finite free-layer axis-graph cubic-box decay

This file consumes the finite free-layer open-slab decay theorem together with
the finite cubic-box transport bridge.  The resulting estimates live on the
induced finite volume of the longitudinal-only free-layer axis graph.  They do
not assert decay for the full cubic lattice graph, where transverse edges are
present, and they do not take a thermodynamic limit.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

/-! ## Cubic-box two-point sets -/

/-- The finite open-slab two-point set at the centre layer and the layer at
longitudinal separation `sep` in the cubic-box normalization. -/
def freeLayerOpenCubicSlabTwoPoint
    (d N sep : ℕ) (hsepN : sep ≤ N) (x : CubicLayerSite d N) :
    Finset (LayerOpenSlabSite (2 * N) (CubicLayerSite d N)) :=
  {Prod.mk (freeLayerOpenCubicLeftIndex N) x,
    Prod.mk (freeLayerOpenCubicRightIndex N sep hsepN) x}

/-- The transported two-point set in the induced finite volume of the
longitudinal-only free-layer axis graph. -/
def freeLayerOpenCubicAxisTwoPoint
    (d N sep : ℕ) (hsepN : sep ≤ N) (x : CubicLayerSite d N) :
    Finset ↑(Ambient.cubicBox (d + 1) N) :=
  (freeLayerOpenCubicSlabTwoPoint d N sep hsepN x).map
    (freeLayerOpenSlabCubicBoxEquiv d N).toEmbedding

/-! ## Slab-length cast transport -/

/-- Relabel an open slab through an equality of its longitudinal step count. -/
private def layerOpenSlabSiteCastEquiv (S : Type*) {n m : ℕ} (h : n = m) :
    LayerOpenSlabSite n S ≃ LayerOpenSlabSite m S :=
  Equiv.prodCongr (finCongr (congrArg Nat.succ h)) (Equiv.refl S)

/-- A bound is unchanged after relabelling an open slab through an equality of
the longitudinal step count. -/
private theorem abs_correlation_layerOpenSlabGraph_cast_le
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (E : Finset (S × S))
    (p : IsingParams ℝ) {n m : ℕ} (h : n = m)
    (A : Finset (LayerOpenSlabSite n S)) {C : ℝ}
    (hA :
      |correlation (layerOpenSlabGraph (S := S) H E n) p A| ≤ C) :
    |correlation (layerOpenSlabGraph (S := S) H E m) p
        (A.map (layerOpenSlabSiteCastEquiv S h).toEmbedding)| ≤ C := by
  subst m
  have hmap :
      A.map (layerOpenSlabSiteCastEquiv S rfl).toEmbedding = A := by
    ext a
    simp [layerOpenSlabSiteCastEquiv]
  simpa [hmap] using hA

/-! ## Finite open-slab cubic-index consumers -/

/-- Finite open-slab free-layer decay in cubic-box coordinates. -/
theorem correlation_freeLayerOpenSlabGraph_cubicBox_same_transverse_abs_le_tanh_clean
    (d N : ℕ) (p : IsingParams ℝ)
    (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : CubicLayerSite d N) (sep : ℕ)
    (hsep : 0 < sep) (hsepN : sep ≤ N) :
    |correlation
      (layerOpenSlabGraph (S := CubicLayerSite d N)
        (⊥ : SimpleGraph (CubicLayerSite d N))
        (layerIdentityTransitionPairs (CubicLayerSite d N)) (2 * N)) p
      (freeLayerOpenCubicSlabTwoPoint d N sep hsepN x)|
      ≤ Real.tanh (p.β * p.J) ^ sep := by
  have hraw :=
    correlation_freeLayerOpenSlabGraph_same_transverse_abs_le_tanh_clean
      (S := CubicLayerSite d N) p hp hβJ x N sep (N - sep) hsep
  have hsteps : N + sep + (N - sep) = 2 * N := by
    omega
  let Araw :
      Finset (LayerOpenSlabSite (N + sep + (N - sep)) (CubicLayerSite d N)) :=
    {Prod.mk (layerOpenLeftIndex N sep (N - sep)) x,
      Prod.mk (layerOpenRightIndex N sep (N - sep)) x}
  have hcast :=
    abs_correlation_layerOpenSlabGraph_cast_le
      (S := CubicLayerSite d N)
      (⊥ : SimpleGraph (CubicLayerSite d N))
      (layerIdentityTransitionPairs (CubicLayerSite d N)) p hsteps Araw hraw
  simpa [freeLayerOpenCubicSlabTwoPoint, freeLayerOpenCubicLeftIndex,
    freeLayerOpenCubicRightIndex, layerOpenLeftIndex, layerOpenRightIndex,
    layerOpenSlabSiteCastEquiv, Araw] using hcast

/-- Mass-form finite open-slab free-layer decay in cubic-box coordinates. -/
theorem correlation_freeLayerOpenSlabGraph_cubicBox_same_transverse_abs_le_exp_neg_mass
    (d N : ℕ) (p : IsingParams ℝ)
    (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : CubicLayerSite d N) (sep : ℕ)
    (hsep : 0 < sep) (hsepN : sep ≤ N) :
    |correlation
      (layerOpenSlabGraph (S := CubicLayerSite d N)
        (⊥ : SimpleGraph (CubicLayerSite d N))
        (layerIdentityTransitionPairs (CubicLayerSite d N)) (2 * N)) p
      (freeLayerOpenCubicSlabTwoPoint d N sep hsepN x)|
      ≤ Real.exp (-(correlationMass (p.β * p.J)) * sep) := by
  have hraw :=
    correlation_freeLayerOpenSlabGraph_same_transverse_abs_le_exp_neg_mass
      (S := CubicLayerSite d N) p hp hβJ x N sep (N - sep) hsep
  have hsteps : N + sep + (N - sep) = 2 * N := by
    omega
  let Araw :
      Finset (LayerOpenSlabSite (N + sep + (N - sep)) (CubicLayerSite d N)) :=
    {Prod.mk (layerOpenLeftIndex N sep (N - sep)) x,
      Prod.mk (layerOpenRightIndex N sep (N - sep)) x}
  have hcast :=
    abs_correlation_layerOpenSlabGraph_cast_le
      (S := CubicLayerSite d N)
      (⊥ : SimpleGraph (CubicLayerSite d N))
      (layerIdentityTransitionPairs (CubicLayerSite d N)) p hsteps Araw hraw
  simpa [freeLayerOpenCubicSlabTwoPoint, freeLayerOpenCubicLeftIndex,
    freeLayerOpenCubicRightIndex, layerOpenLeftIndex, layerOpenRightIndex,
    layerOpenSlabSiteCastEquiv, Araw] using hcast

/-! ## Induced axis-graph cubic-box consumers -/

/-- The finite free-layer open decay bound transported to the induced cubic box
of the longitudinal-only axis graph. -/
theorem correlation_induced_freeLayerAxisGraph_cubicBox_same_transverse_abs_le_tanh_clean
    (d N : ℕ) (p : IsingParams ℝ)
    (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : CubicLayerSite d N) (sep : ℕ)
    (hsep : 0 < sep) (hsepN : sep ≤ N) :
    |correlation
      (Ambient.inducedGraph (freeLayerAxisGraph d)
        (Ambient.cubicBox (d + 1) N)) p
      (freeLayerOpenCubicAxisTwoPoint d N sep hsepN x)|
      ≤ Real.tanh (p.β * p.J) ^ sep := by
  exact
    abs_correlation_induced_freeLayerAxisGraph_cubicBox_le_of_openSlab
      d N p (freeLayerOpenCubicSlabTwoPoint d N sep hsepN x)
      (correlation_freeLayerOpenSlabGraph_cubicBox_same_transverse_abs_le_tanh_clean
        d N p hp hβJ x sep hsep hsepN)

/-- Mass-form finite free-layer open decay transported to the induced cubic box
of the longitudinal-only axis graph. -/
theorem correlation_induced_freeLayerAxisGraph_cubicBox_same_transverse_abs_le_exp_neg_mass
    (d N : ℕ) (p : IsingParams ℝ)
    (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : CubicLayerSite d N) (sep : ℕ)
    (hsep : 0 < sep) (hsepN : sep ≤ N) :
    |correlation
      (Ambient.inducedGraph (freeLayerAxisGraph d)
        (Ambient.cubicBox (d + 1) N)) p
      (freeLayerOpenCubicAxisTwoPoint d N sep hsepN x)|
      ≤ Real.exp (-(correlationMass (p.β * p.J)) * sep) := by
  exact
    abs_correlation_induced_freeLayerAxisGraph_cubicBox_le_of_openSlab
      d N p (freeLayerOpenCubicSlabTwoPoint d N sep hsepN x)
      (correlation_freeLayerOpenSlabGraph_cubicBox_same_transverse_abs_le_exp_neg_mass
        d N p hp hβJ x sep hsep hsepN)

end TransferMatrix

end IsingModel
