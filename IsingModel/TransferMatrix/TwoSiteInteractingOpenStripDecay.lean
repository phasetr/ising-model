import IsingModel.TransferMatrix.TwoSiteInteractingOpenStripTransport
import IsingModel.TransferMatrix.TwoSiteInteractingLayerOpenDecay

/-!
# Two-site interacting open strip decay on the ambient lattice

This file transports the finite interacting `K2` open-slab decay bounds of
`TwoSiteInteractingLayerOpenBoundaryWindow` / `TwoSiteInteractingLayerOpenDecay`
onto the induced finite volume of the ambient lattice graph `latticeGraph 2` on
the two-row strip `twoSiteOpenStrip`, using the graph/correlation transport of
`TwoSiteInteractingOpenStripTransport`.  The two correlated endpoints become the
strip points `![(left : ℤ), (x : ℤ)]` and `![(left + sep : ℤ), (x : ℤ)]`.

The results are finite.  They do not pass to a thermodynamic limit or prove
final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

/-! ## Transport of a correlation bound -/

/-- A finite `K2` open-slab correlation bound transports to the induced finite
volume of the ambient `latticeGraph 2` on the two-row strip. -/
theorem abs_correlation_induced_latticeGraph_two_strip_le_of_openSlab
    (n : ℕ) (p : IsingParams ℝ)
    (A : Finset (LayerOpenSlabSite n (Fin 2))) {C : ℝ}
    (hA : |correlation (layerOpenSlabGraph (S := Fin 2) (SimpleGraph.completeGraph (Fin 2))
        (layerIdentityTransitionPairs (Fin 2)) n) p A| ≤ C) :
    |correlation (Ambient.inducedGraph (latticeGraph 2) (twoSiteOpenStrip n)) p
        (A.map (twoSiteOpenStripEquiv n).toEmbedding)| ≤ C := by
  rw [abs_correlation_induced_latticeGraph_two_strip_eq_openSlab]
  exact hA

/-! ## The transported two-point observable -/

/-- The `K2` open-slab same-transverse-site two-point observable. -/
def twoSiteInteractingOpenSlabTwoPoint (x : Fin 2) (left sep right : ℕ) :
    Finset (LayerOpenSlabSite (left + sep + right) (Fin 2)) :=
  {Prod.mk (layerOpenLeftIndex left sep right) x,
    Prod.mk (layerOpenRightIndex left sep right) x}

/-- The transported strip two-point observable. -/
noncomputable def twoSiteInteractingOpenStripTwoPoint (x : Fin 2) (left sep right : ℕ) :
    Finset ↑(twoSiteOpenStrip (left + sep + right)) :=
  (twoSiteInteractingOpenSlabTwoPoint x left sep right).map
    (twoSiteOpenStripEquiv (left + sep + right)).toEmbedding

/-- The transported left endpoint is the strip point `![left, x]`. -/
@[simp]
theorem twoSiteOpenStripPoint_left (x : Fin 2) (left sep right : ℕ) :
    twoSiteOpenStripPoint (left + sep + right)
        (layerOpenLeftIndex left sep right, x)
      = ![(left : ℤ), (x.val : ℤ)] := by
  rw [twoSiteOpenStripPoint, layerOpenLeftIndex]

/-- The transported right endpoint is the strip point `![left + sep, x]`. -/
@[simp]
theorem twoSiteOpenStripPoint_right (x : Fin 2) (left sep right : ℕ) :
    twoSiteOpenStripPoint (left + sep + right)
        (layerOpenRightIndex left sep right, x)
      = ![((left + sep : ℕ) : ℤ), (x.val : ℤ)] := by
  rw [twoSiteOpenStripPoint, layerOpenRightIndex]

/-! ## Transported interacting open-strip decay -/

/-- Prefactor-form interacting decay on the induced ambient `latticeGraph 2`
strip. -/
theorem correlation_induced_latticeGraph_two_strip_abs_le_of_simpleSpectrum
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : Fin 2) (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (Ambient.inducedGraph (latticeGraph 2)
          (twoSiteOpenStrip (left + sep + right))) p
        (twoSiteInteractingOpenStripTwoPoint x left sep right)|
      ≤
        ((twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryMarkedSpectralPrefactor
            (layerSpinAt x)
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p)) /
          (twoSiteInteractingLayerOrthogonalSpectralData p hp).boundarySpectralPartitionPrefactor
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
            twoSiteInteractingLayerTop (twoSiteInteractingTheta (p.β * p.J))) *
          twoSiteInteractingTheta (p.β * p.J) ^ sep :=
  abs_correlation_induced_latticeGraph_two_strip_le_of_openSlab _ p
    (twoSiteInteractingOpenSlabTwoPoint x left sep right)
    (correlation_twoSiteInteractingLayerOpenSlabGraph_abs_le_of_simpleSpectrum
      p hp hβJ x left sep right hsep)

/-- Mass-form interacting decay on the induced ambient `latticeGraph 2` strip:
finite decay with rate `m = -log(flipOdd / top)`. -/
theorem correlation_induced_latticeGraph_two_strip_abs_le_exp_neg_mass
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : Fin 2) (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (Ambient.inducedGraph (latticeGraph 2)
          (twoSiteOpenStrip (left + sep + right))) p
        (twoSiteInteractingOpenStripTwoPoint x left sep right)|
      ≤
        ((twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryMarkedSpectralPrefactor
            (layerSpinAt x)
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p)) /
          (twoSiteInteractingLayerOrthogonalSpectralData p hp).boundarySpectralPartitionPrefactor
            (layerOpenBalancedBoundaryVector
              (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
            twoSiteInteractingLayerTop (twoSiteInteractingTheta (p.β * p.J))) *
          Real.exp (-(twoSiteInteractingMass (p.β * p.J)) * sep) :=
  abs_correlation_induced_latticeGraph_two_strip_le_of_openSlab _ p
    (twoSiteInteractingOpenSlabTwoPoint x left sep right)
    (correlation_twoSiteInteractingLayerOpenSlabGraph_abs_le_exp_neg_mass
      p hp hβJ x left sep right hsep)

end TransferMatrix

end IsingModel
