import IsingModel.TransferMatrix.TwoSiteInteractingLayerOpenBoundaryWindow

/-!
# Two-site interacting open strip mass decay

This file packages the finite interacting `K2` open-slab decay of
`TwoSiteInteractingLayerOpenBoundaryWindow` in mass form, matching the
`exp(-m·sep)` language used by §17.5 and the free-layer wrappers.  The decay
parameter `theta = flipOdd / top` lies strictly in `(0, 1)` for `0 < βJ`, so the
decay mass `m = -log(theta) = log(top/flipOdd)` is positive and
`theta ^ sep = exp(-m·sep)`.

The results are finite.  They do not prove a closed-form rate beyond `-log θ`, a
thermodynamic limit, or final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

/-! ## The interacting decay mass -/

/-- The decay parameter `theta = flipOdd / top` is positive for `0 < a`. -/
theorem twoSiteInteractingTheta_pos {a : ℝ} (ha : 0 < a) :
    0 < twoSiteInteractingTheta a :=
  div_pos (twoSiteK2FlipOdd_pos ha) (twoSiteK2Top_pos a)

/-- The interacting open-slab decay mass `m = -log(theta)`. -/
noncomputable def twoSiteInteractingMass (a : ℝ) : ℝ :=
  -Real.log (twoSiteInteractingTheta a)

/-- The decay mass is positive for `0 < a`, since `0 < theta < 1`. -/
theorem twoSiteInteractingMass_pos {a : ℝ} (ha : 0 < a) :
    0 < twoSiteInteractingMass a := by
  rw [twoSiteInteractingMass]
  exact neg_pos.mpr
    (Real.log_neg (twoSiteInteractingTheta_pos ha) (twoSiteInteractingTheta_lt_one a))

/-- The decay mass equals `log(top / flipOdd)`. -/
theorem twoSiteInteractingMass_eq_log_top_div_flipOdd (a : ℝ) :
    twoSiteInteractingMass a = Real.log (twoSiteK2Top a / twoSiteK2FlipOdd a) := by
  rw [twoSiteInteractingMass, twoSiteInteractingTheta,
    ← Real.log_inv, inv_div]

/-- The `sep`-th power of the decay parameter is the mass exponential. -/
theorem twoSiteInteractingTheta_pow_eq_exp_neg_mass {a : ℝ} (ha : 0 < a) (n : ℕ) :
    twoSiteInteractingTheta a ^ n = Real.exp (-(twoSiteInteractingMass a) * n) := by
  rw [twoSiteInteractingMass, neg_neg]
  rw [show Real.log (twoSiteInteractingTheta a) * (n : ℝ)
      = (n : ℝ) * Real.log (twoSiteInteractingTheta a) from mul_comm _ _]
  rw [Real.exp_nat_mul, Real.exp_log (twoSiteInteractingTheta_pos ha)]

/-! ## Mass-form open-slab decay -/

/-- The mass-form interacting open-slab same-transverse-site correlation bound:
finite decay with rate `m = -log(flipOdd / top)`. -/
theorem correlation_twoSiteInteractingLayerOpenSlabGraph_abs_le_exp_neg_mass
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : Fin 2) (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation
        (layerOpenSlabGraph (S := Fin 2) (SimpleGraph.completeGraph (Fin 2))
          (layerIdentityTransitionPairs (Fin 2)) (left + sep + right)) p
        ({Prod.mk (layerOpenLeftIndex left sep right) x,
          Prod.mk (layerOpenRightIndex left sep right) x} :
            Finset (LayerOpenSlabSite (left + sep + right) (Fin 2)))|
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
          Real.exp (-(twoSiteInteractingMass (p.β * p.J)) * sep) := by
  rw [← twoSiteInteractingTheta_pow_eq_exp_neg_mass hβJ sep]
  exact correlation_twoSiteInteractingLayerOpenSlabGraph_abs_le_of_simpleSpectrum
    p hp hβJ x left sep right hsep

end TransferMatrix

end IsingModel
