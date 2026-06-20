import IsingModel.TransferMatrix.LayerProjectiveDiameter
import IsingModel.TransferMatrix.CubicLayerCardinalitySmallRatio

/-!
# Site factorization of the identity-transition projective cross-ratio

The identity-transition layer kernel
`k ω η = exp(βJ ∑_x s(ω x) s(η x))` factorizes over the transverse sites, so its
projective cross-ratio is a single exponential of a **sum over sites**:
`cr(k; ω, ω', η, η') = exp(βJ ∑_x (s(ω x) − s(ω' x))·(s(η x) − s(η' x)))`.
By the row/column scaling invariance of `LayerProjectiveDiameter`, the Doob
transform of the balanced cubic transfer matrix has the same cross-ratio — so it
too is this site-additive exponential, independent of both the layer weight `u`
and the Perron vector `w`.

This makes the structure of the Hilbert-metric route explicit: the log
cross-ratio is **additive over transverse sites**, with each site contributing at
most `4·|βJ|`.  In particular the *global* projective diameter grows linearly in
the number of transverse sites, which is precisely why a transverse-volume-uniform
gap cannot come from the global Dobrushin/diameter bound alone; a uniform estimate
must exploit the site-tensorized structure (a local / tensorized contraction), the
subject of a later research arc.

The results are finite algebraic identities and bounds.  They do not give a
transverse-volume-uniform gap, prove a thermodynamic limit, or prove final
hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The identity-transition layer kernel is the exponential of a sum over sites. -/
theorem layerTransitionWeight_identity_eq_exp_sum (p : IsingParams ℝ)
    (ω η : LayerState S) :
    layerTransitionWeight (layerIdentityTransitionPairs S) p ω η
      = Real.exp (p.β * p.J * ∑ x, Spin.sign ℝ (ω x) * Spin.sign ℝ (η x)) := by
  rw [layerTransitionWeight, layerIdentityTransitionPairs]
  congr 2
  rw [Finset.sum_image (fun a _ b _ h => congr_arg Prod.fst h)]

/-- **Site factorization of the identity-transition cross-ratio.**  The projective
cross-ratio of the identity-transition kernel is the exponential of a site sum. -/
theorem matrixProjectiveCrossRatio_layerTransitionWeight_identity (p : IsingParams ℝ)
    (ω ω' η η' : LayerState S) :
    matrixProjectiveCrossRatio (layerTransitionWeight (layerIdentityTransitionPairs S) p)
        ω ω' η η'
      = Real.exp (p.β * p.J *
          ∑ x, (Spin.sign ℝ (ω x) - Spin.sign ℝ (ω' x)) *
            (Spin.sign ℝ (η x) - Spin.sign ℝ (η' x))) := by
  rw [matrixProjectiveCrossRatio, layerTransitionWeight_identity_eq_exp_sum,
    layerTransitionWeight_identity_eq_exp_sum, layerTransitionWeight_identity_eq_exp_sum,
    layerTransitionWeight_identity_eq_exp_sum, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_sub, Real.exp_eq_exp]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The Doob transform of the balanced cubic transfer matrix has the same
identity-transition cross-ratio: a site-additive exponential independent of both
the layer weight `u` and the Perron vector `w`. -/
theorem matrixProjectiveCrossRatio_doob_cubic_identity_eq_exp_sum
    (d R : ℕ) (p : IsingParams ℝ) {lam : ℝ} (hlam : 0 < lam)
    {w : LayerState (CubicLayerSite d R) → ℝ} (hw : VectorPositive w)
    (ω ω' η η' : LayerState (CubicLayerSite d R)) :
    matrixProjectiveCrossRatio
        (matrixDoobTransform
          (layerSymmetricTransferMatrix
            (layerInternalWeight (cubicLayerGraph d R) p)
            (layerTransitionWeight (cubicLayerTransitionPairs d R) p))
          lam w)
        ω ω' η η'
      = Real.exp (p.β * p.J *
          ∑ x, (Spin.sign ℝ (ω x) - Spin.sign ℝ (ω' x)) *
            (Spin.sign ℝ (η x) - Spin.sign ℝ (η' x))) := by
  rw [matrixProjectiveCrossRatio_matrixDoobTransform_layerSymmetricTransferMatrix
      (cubicLayerInternalWeight_pos d R p) (cubicLayerTransitionWeight_pos d R p) hlam hw]
  exact matrixProjectiveCrossRatio_layerTransitionWeight_identity p ω ω' η η'

end TransferMatrix

end IsingModel
