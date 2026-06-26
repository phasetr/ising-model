import IsingModel.TransferMatrix.LayerOpenExplicitSubdominantRatio
import IsingModel.TransferMatrix.CubicLayerOpenBoxMass

/-!
# Mass-form decay on the ambient cubic open box, explicit ratio (GJ §17.1)

The explicit-ratio cubic open-box decay
(`correlation_cubicLayerOpenBox_abs_le_of_hermitianExplicitRatio...`
in `LayerOpenExplicitSubdominantRatio.lean`) is the consumer that a
transverse-volume-uniform high-temperature estimate feeds, since its decay parameter
`cubicLayerHermitianExplicitRatio` is controlled directly by any quantitative eigenvalue
bound.  This file recasts that decay in the **mass form** `exp(-mass·sep)` with
`mass = -log(explicit ratio)`, the explicit-ratio companion of
`correlation_induced_latticeGraph_cubicLayerOpenBox_abs_le_exp_neg_mass`.

As with the canonical-ratio mass form, the explicit subdominant ratio is only known to
satisfy `0 ≤ ratio < 1`, so the mass form additionally assumes `0 < ratio`.

* `cubicLayerHermitianExplicitMass`, `cubicLayerHermitianExplicitMass_pos`,
  `cubicLayerHermitianExplicitRatio_pow_eq_exp_neg_mass`.
* `correlation_induced_latticeGraph_cubicLayerOpenBox_abs_le_exp_neg_explicitMass`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp.~304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp.~311--312.
-/

namespace IsingModel

namespace TransferMatrix

/-- **The cubic-layer explicit decay mass.**  `mass = -log(explicit ratio)`, where the
explicit ratio is the genuine finite maximum of `|λ_i|/λ_top` over the non-maximal
spectral indices of the cubic transverse layer Hermitian spectral data. -/
noncomputable def cubicLayerHermitianExplicitMass (d R : ℕ) (p : IsingParams ℝ) : ℝ :=
  -Real.log (cubicLayerHermitianExplicitRatio d R p)

/-- The explicit decay mass is positive when the explicit ratio is positive (and `< 1`). -/
theorem cubicLayerHermitianExplicitMass_pos (d R : ℕ) (p : IsingParams ℝ)
    (hpos : 0 < cubicLayerHermitianExplicitRatio d R p) :
    0 < cubicLayerHermitianExplicitMass d R p := by
  rw [cubicLayerHermitianExplicitMass]
  exact neg_pos.mpr (Real.log_neg hpos (cubicLayerHermitianExplicitRatio_lt_one d R p))

/-- The `sep`-th power of the explicit ratio is the explicit-mass exponential. -/
theorem cubicLayerHermitianExplicitRatio_pow_eq_exp_neg_mass (d R : ℕ) (p : IsingParams ℝ)
    (hpos : 0 < cubicLayerHermitianExplicitRatio d R p) (n : ℕ) :
    cubicLayerHermitianExplicitRatio d R p ^ n
      = Real.exp (-(cubicLayerHermitianExplicitMass d R p) * n) := by
  rw [cubicLayerHermitianExplicitMass, neg_neg,
    show Real.log (cubicLayerHermitianExplicitRatio d R p) * (n : ℝ)
        = (n : ℝ) * Real.log (cubicLayerHermitianExplicitRatio d R p) from mul_comm _ _,
    Real.exp_nat_mul, Real.exp_log hpos]

/-- **Mass-form finite cubic open-box decay on the ambient lattice, explicit ratio.**  The
explicit-ratio cubic open-box decay recast with the mass exponential `exp(-mass·sep)`,
`mass = -log(explicit ratio)`.  The explicit decay parameter is controlled directly by any
quantitative eigenvalue estimate, so this is the mass-form consumer a transverse-volume
-uniform high-temperature estimate will feed.  Adds the hypothesis
`0 < cubicLayerHermitianExplicitRatio d R p`.  Finite and conditional on the boundary
window gap and the columnwise-simple-eigenspace parity input, at zero field; it does not
construct the uniform window or pass to a thermodynamic limit. -/
theorem correlation_induced_latticeGraph_cubicLayerOpenBox_abs_le_exp_neg_explicitMass
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0) (x : CubicLayerSite d R)
    (hwindow :
      cubicLayerHermitianExplicitRatio d R p <
        layerOpenBoundarySpectralWindowCap (layerInternalWeight (cubicLayerGraph d R) p)
          (cubicLayerHermitianData d R p) (cubicLayerHermitianData d R p).maxEigenIndex)
    (hsimple : (cubicLayerHermitianData d R p).ColumnSimpleEigenspaces)
    (hpos : 0 < cubicLayerHermitianExplicitRatio d R p)
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
            (cubicLayerHermitianData d R p).maxEigenIndex
            (cubicLayerHermitianExplicitRatio d R p)) *
          Real.exp (-(cubicLayerHermitianExplicitMass d R p) * sep) := by
  rw [← cubicLayerHermitianExplicitRatio_pow_eq_exp_neg_mass d R p hpos sep,
    cubicLayerOpenBoxTwoPoint,
    abs_correlation_induced_latticeGraph_cubicLayerOpenBox_eq_openSlab]
  exact correlation_layerOpenSlabGraph_abs_le_of_hermitianExplicitRatioSimpleParityWindow
    (cubicLayerGraph d R) (cubicLayerTransitionPairs d R) p hp x
    (cubicLayerTransitionWeight_symm d R p) hwindow hsimple left sep right hsep

end TransferMatrix

end IsingModel
