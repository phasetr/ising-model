import IsingModel.TransferMatrix.CubicLayerOpenBoxTransport

/-!
# Mass-form decay on the ambient cubic open box (GJ §17.1)

The arbitrary finite transverse layer open-box decay of `CubicLayerOpenBoxTransport.lean`
(the induced-lattice box-transport theorem
`correlation_cubicLayerOpenBox_abs_le_of_...`) is stated with the
geometric factor `ratio^sep` (the canonical maximal-index
subdominant ratio `cubicLayerHermitianRatio d R p`).  This file recasts it in the
**mass form** `exp(-mass·sep)` with `mass = -log(ratio)`, mirroring the `K2` mass form
`correlation_induced_latticeGraph_two_strip_abs_le_exp_neg_mass`.

Since the canonical subdominant ratio is only known to satisfy `0 ≤ ratio < 1`, the mass
form additionally assumes `0 < ratio` (so that `mass = -log ratio` is well-defined and
positive); the conversion is `ratio^sep = exp(-mass·sep)`.

* `cubicLayerHermitianMass`, `cubicLayerHermitianMass_pos`,
  `cubicLayerHermitianRatio_pow_eq_exp_neg_mass`.
* `correlation_induced_latticeGraph_cubicLayerOpenBox_abs_le_exp_neg_mass`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp.~304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp.~311--312.
-/

namespace IsingModel

namespace TransferMatrix

/-- **The cubic-layer decay mass.**  `mass = -log(ratio)`, where `ratio` is the canonical
maximal-index subdominant ratio of the cubic transverse layer Hermitian spectral data. -/
noncomputable def cubicLayerHermitianMass (d R : ℕ) (p : IsingParams ℝ) : ℝ :=
  -Real.log (cubicLayerHermitianRatio d R p)

/-- The decay mass is positive when the subdominant ratio is positive (and `< 1`). -/
theorem cubicLayerHermitianMass_pos (d R : ℕ) (p : IsingParams ℝ)
    (hpos : 0 < cubicLayerHermitianRatio d R p) :
    0 < cubicLayerHermitianMass d R p := by
  rw [cubicLayerHermitianMass]
  exact neg_pos.mpr (Real.log_neg hpos
    (finiteTransverseHermitianRatio_lt_one (cubicLayerGraph d R)
      (cubicLayerTransitionPairs d R) p (cubicLayerTransitionWeight_symm d R p)))

/-- The `sep`-th power of the subdominant ratio is the mass exponential. -/
theorem cubicLayerHermitianRatio_pow_eq_exp_neg_mass (d R : ℕ) (p : IsingParams ℝ)
    (hpos : 0 < cubicLayerHermitianRatio d R p) (n : ℕ) :
    cubicLayerHermitianRatio d R p ^ n
      = Real.exp (-(cubicLayerHermitianMass d R p) * n) := by
  rw [cubicLayerHermitianMass, neg_neg,
    show Real.log (cubicLayerHermitianRatio d R p) * (n : ℝ)
        = (n : ℝ) * Real.log (cubicLayerHermitianRatio d R p) from mul_comm _ _,
    Real.exp_nat_mul, Real.exp_log hpos]

/-- **Mass-form finite cubic open-box decay on the ambient lattice.**  The Phase-6 cubic
open-box decay recast with the mass exponential `exp(-mass·sep)`, `mass = -log(ratio)`.
Adds the hypothesis `0 < cubicLayerHermitianRatio d R p` (so that the mass is well-defined
and positive).  Like the `ratio^sep` form, this is finite and conditional on the boundary
window gap and the columnwise-simple-eigenspace parity input, at zero field; it does not
construct the uniform-in-transverse-volume window and does not pass to a thermodynamic
limit. -/
theorem correlation_induced_latticeGraph_cubicLayerOpenBox_abs_le_exp_neg_mass
    (d R : ℕ) (p : IsingParams ℝ) (hp : p.h = 0) (x : CubicLayerSite d R)
    (hwindow :
      cubicLayerHermitianRatio d R p <
        layerOpenBoundarySpectralWindowCap (layerInternalWeight (cubicLayerGraph d R) p)
          (cubicLayerHermitianData d R p) (cubicLayerHermitianData d R p).maxEigenIndex)
    (hsimple : (cubicLayerHermitianData d R p).ColumnSimpleEigenspaces)
    (hpos : 0 < cubicLayerHermitianRatio d R p)
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
          Real.exp (-(cubicLayerHermitianMass d R p) * sep) := by
  rw [← cubicLayerHermitianRatio_pow_eq_exp_neg_mass d R p hpos sep, cubicLayerOpenBoxTwoPoint,
    abs_correlation_induced_latticeGraph_cubicLayerOpenBox_eq_openSlab]
  exact correlation_cubicLayerOpenSlabGraph_abs_le_of_hermitianCanonicalRatioSimpleParityWindow
    d R p hp x (cubicLayerTransitionWeight_symm d R p) hwindow hsimple left sep right hsep

end TransferMatrix

end IsingModel
