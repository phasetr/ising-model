import IsingModel.ContinuousSpin.TwoComponentDoubledWeight
import IsingModel.ContinuousSpin.TwoComponentGriffithsVII
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The duplicate-variable change of variables is measure-preserving (GJ Thm 4.7.1)

The combined map `(ξ, ξ') ↦ cfg`, `cfg i = rotLin (dCoord ξ ξ' i)`, sending the
doubled two-component configuration to its block-rotated form, is measure-preserving
from `(volume.prod volume)` on `VectorConfig ι × VectorConfig ι` to `volume` on
`(ι → Fin 4 → ℝ)`.  This is the measure side of the duplicate-variable reduction
for the second/third inequalities of GJ Theorem 4.7.1 (4.7.6)–(4.7.8).

The map factors as `rotLinPi ∘ reshape`, where `reshape` reshuffles the doubled
configuration coordinate by coordinate into `(ι → Fin 4 → ℝ)`.  Measure-preservation
of `reshape` is assembled from the standard Mathlib measure-preserving equivalences
(`arrowProdEquivProdArrow`, `finTwoArrow`, `sumPiEquivProdPi`, `piCongrLeft`), and
`rotLinPi` is measure-preserving by `measurePreserving_rotLinPi`.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.7, Theorem 4.7.1, pp. 70–71
-/

namespace IsingModel.ContinuousSpin

open MeasureTheory

variable {ι : Type*}

/-- The per-site reshuffle `((t,q),(t',q')) ↦ ![t,q,t',q']`. -/
noncomputable def siteReshape (p : (ℝ × ℝ) × (ℝ × ℝ)) : Fin 4 → ℝ :=
  ![p.1.1, p.1.2, p.2.1, p.2.2]

/-- The per-site reshuffle is measure-preserving on `((ℝ×ℝ)×(ℝ×ℝ)) ≃ (Fin 4 → ℝ)`. -/
theorem measurePreserving_siteReshape :
    MeasurePreserving siteReshape (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))) volume := by
  have h1 : MeasurePreserving
      (Prod.map (⇑(MeasurableEquiv.finTwoArrow (α := ℝ)).symm)
        (⇑(MeasurableEquiv.finTwoArrow (α := ℝ)).symm))
      (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))) volume :=
    (volume_preserving_finTwoArrow ℝ).symm.prod (volume_preserving_finTwoArrow ℝ).symm
  have h2 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin 2 ⊕ Fin 2 => ℝ)
  have h3 := volume_measurePreserving_piCongrLeft (fun _ : Fin (2 + 2) => ℝ) finSumFinEquiv
  have hcomp := h3.comp (h2.comp h1)
  have hmeas : Measurable siteReshape := by
    refine measurable_pi_iff.2 fun j => ?_
    fin_cases j
    · simpa [siteReshape] using (measurable_fst.comp measurable_fst :
        Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.1)
    · simpa [siteReshape] using (measurable_snd.comp measurable_fst :
        Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.2)
    · simpa [siteReshape] using (measurable_fst.comp measurable_snd :
        Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.2.1)
    · simpa [siteReshape] using (measurable_snd.comp measurable_snd :
        Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.2.2)
  refine hcomp.congr hmeas (Filter.Eventually.of_forall fun p => ?_)
  funext j
  fin_cases j <;>
    simp [siteReshape, Function.comp, MeasurableEquiv.coe_piCongrLeft,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.piCongrLeft_apply_eq_cast,
      finSumFinEquiv, Fin.addCases, Fin.castLT, Fin.subNat]

/-- The per-site reshuffle as a measurable equivalence. -/
noncomputable def siteEquiv : ((ℝ × ℝ) × (ℝ × ℝ)) ≃ᵐ (Fin 4 → ℝ) :=
  ((MeasurableEquiv.finTwoArrow (α := ℝ)).symm.prodCongr
      (MeasurableEquiv.finTwoArrow (α := ℝ)).symm).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (2 + 2) => ℝ) finSumFinEquiv))

/-- The per-site measurable equivalence has the expected coordinate function. -/
theorem coe_siteEquiv : ⇑siteEquiv = siteReshape := by
  funext p j
  fin_cases j <;>
    simp [siteEquiv, siteReshape, MeasurableEquiv.finTwoArrow,
      MeasurableEquiv.piFinTwo, MeasurableEquiv.prodCongr, Equiv.prodCongr,
      piFinTwoEquiv, MeasurableEquiv.coe_piCongrLeft,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.piCongrLeft_apply_eq_cast,
      finSumFinEquiv, Fin.addCases, Fin.castLT, Fin.subNat]

/-- The per-site reshuffle measurable equivalence preserves volume. -/
theorem measurePreserving_siteEquiv :
    MeasurePreserving siteEquiv (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))) volume := by
  simpa [coe_siteEquiv] using measurePreserving_siteReshape

/-- A named invertibility witness for `rotMatrix`, shared by `rotEquiv` and its coe lemma. -/
@[reducible] noncomputable def rotMatrixInvertible : Invertible rotMatrix :=
  Matrix.invertibleOfIsUnitDet rotMatrix (isUnit_iff_ne_zero.mpr rotMatrix_det_ne_zero)

/-- The single-site §4.7 rotation as a measurable equivalence. -/
noncomputable def rotEquiv : (Fin 4 → ℝ) ≃ᵐ (Fin 4 → ℝ) :=
  (Matrix.toLinearEquiv' rotMatrix
    rotMatrixInvertible).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

/-- The rotation measurable equivalence has underlying function `rotLin`. -/
theorem coe_rotEquiv : ⇑rotEquiv = rotLin := by
  rw [rotEquiv, Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph,
    LinearEquiv.coe_toContinuousLinearEquiv']
  change ⇑(Matrix.toLinearEquiv' rotMatrix rotMatrixInvertible : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) =
    ⇑(Matrix.toLin' rotMatrix)
  exact congrArg DFunLike.coe (Matrix.toLinearEquiv'_apply rotMatrix rotMatrixInvertible)

/-- The single-site rotation measurable equivalence preserves volume. -/
theorem measurePreserving_rotEquiv :
    MeasurePreserving rotEquiv (volume : Measure (Fin 4 → ℝ)) volume := by
  simpa [coe_rotEquiv] using measurePreserving_rotLin

/-- The doubled configuration reshuffle followed by the site-wise §4.7 rotation. -/
noncomputable def combinedEquiv [Fintype ι] :
    ((ι → ℝ × ℝ) × (ι → ℝ × ℝ)) ≃ᵐ (ι → Fin 4 → ℝ) :=
  (MeasurableEquiv.arrowProdEquivProdArrow (ℝ × ℝ) (ℝ × ℝ) ι).symm.trans
    ((MeasurableEquiv.piCongrRight (fun _ : ι => siteEquiv)).trans
      (MeasurableEquiv.piCongrRight (fun _ : ι => rotEquiv)))

/-- The combined measurable equivalence is the intended pointwise rotated coordinate map
`(ξ, ξ') ↦ (i ↦ rotLin (dCoord ξ ξ' i))`. -/
theorem coe_combinedEquiv [Fintype ι] :
    ⇑(combinedEquiv : ((ι → ℝ × ℝ) × (ι → ℝ × ℝ)) ≃ᵐ (ι → Fin 4 → ℝ))
      = (fun p i => rotLin (dCoord p.1 p.2 i)) := by
  funext p i
  simp [combinedEquiv, coe_rotEquiv, coe_siteEquiv, siteReshape, dCoord,
    MeasurableEquiv.arrowProdEquivProdArrow, MeasurableEquiv.piCongrRight,
    Equiv.arrowProdEquivProdArrow]

/-- The combined measurable equivalence preserves volume. -/
theorem measurePreserving_combinedEquiv [Fintype ι] :
    MeasurePreserving (combinedEquiv : ((ι → ℝ × ℝ) × (ι → ℝ × ℝ)) ≃ᵐ (ι → Fin 4 → ℝ))
      (volume : Measure ((ι → ℝ × ℝ) × (ι → ℝ × ℝ))) volume := by
  have h0 : MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow (ℝ × ℝ) (ℝ × ℝ) ι).symm
      (volume : Measure ((ι → ℝ × ℝ) × (ι → ℝ × ℝ))) volume :=
    (volume_measurePreserving_arrowProdEquivProdArrow (ℝ × ℝ) (ℝ × ℝ) ι).symm
  have h1 : MeasurePreserving
      (fun x : ι → (ℝ × ℝ) × (ℝ × ℝ) => fun i => siteEquiv (x i))
      (volume : Measure (ι → (ℝ × ℝ) × (ℝ × ℝ))) volume :=
    volume_preserving_pi (fun _ : ι => measurePreserving_siteEquiv)
  have h2 : MeasurePreserving
      (fun x : ι → Fin 4 → ℝ => fun i => rotEquiv (x i))
      (volume : Measure (ι → Fin 4 → ℝ)) volume :=
    volume_preserving_pi (fun _ : ι => measurePreserving_rotEquiv)
  exact h2.comp (h1.comp h0)

/-- The combined pointwise coordinate map preserves volume. -/
theorem measurePreserving_combinedMap [Fintype ι] :
    MeasurePreserving (fun (p : (ι → ℝ × ℝ) × (ι → ℝ × ℝ)) (i : ι) => rotLin (dCoord p.1 p.2 i))
      (volume : Measure ((ι → ℝ × ℝ) × (ι → ℝ × ℝ))) volume := by
  simpa [coe_combinedEquiv] using (measurePreserving_combinedEquiv (ι := ι))

/-- **The doubled Gibbs integral of a non-negative-coefficient difference observable is
non-negative** (GJ Theorem 4.7.1 (4.7.6)–(4.7.8), pp. 70–71).  If the doubled product of
observable differences `(F(ξ)−F(ξ'))·(G(ξ)−G(ξ'))` equals the doubled-rotated evaluation
`dSpinEval obs` of a non-negative-coefficient polynomial `obs`, then the doubled Gibbs integral
is non-negative.  This is the engine of the second/third inequalities: the duplicate-variable
change of variables (`measurePreserving_combinedEquiv`), the weight factorization
(`vectorWeight_mul_eq_rot`), and the doubled-rotated cone non-negativity
(`dRotInteraction_nonneg`) combine into a single positivity statement. -/
theorem doubled_integral_nonneg [Fintype ι] (Gr : SimpleGraph ι) [Fintype Gr.edgeSet]
    {A σ J h1 h2 β : ℝ} (hA : 0 < A) (hβJ : 0 ≤ β * J)
    (hcα : 0 ≤ Real.sqrt 2 * β * h1) (hcγ : 0 ≤ Real.sqrt 2 * β * h2)
    {F G : VectorConfig ι → ℝ} {obs : MvPolynomial (ι × Fin 4) ℝ} (hobs : NNCoeffs obs)
    (hid : ∀ ξ ξ' : VectorConfig ι,
      (F ξ - F ξ') * (G ξ - G ξ') = dSpinEval obs (fun i => rotLin (dCoord ξ ξ' i))) :
    0 ≤ ∫ z : VectorConfig ι × VectorConfig ι,
        (F z.1 - F z.2) * (G z.1 - G z.2)
          * vectorWeight Gr A σ J h1 h2 β z.1 * vectorWeight Gr A σ J h1 h2 β z.2 := by
  have hkey : (∫ z : VectorConfig ι × VectorConfig ι,
      (F z.1 - F z.2) * (G z.1 - G z.2)
        * vectorWeight Gr A σ J h1 h2 β z.1 * vectorWeight Gr A σ J h1 h2 β z.2)
      = ∫ cfg : ι → Fin 4 → ℝ, dSpinEval obs cfg
          * Real.exp (β * J * ∑ e ∈ Gr.edgeFinset, edgeDot4 cfg e)
          * ∏ i, siteWeight4 A σ (Real.sqrt 2 * β * h1) (Real.sqrt 2 * β * h2) (cfg i) := by
    rw [← (measurePreserving_combinedEquiv (ι := ι)).integral_comp'
      (fun cfg => dSpinEval obs cfg
        * Real.exp (β * J * ∑ e ∈ Gr.edgeFinset, edgeDot4 cfg e)
        * ∏ i, siteWeight4 A σ (Real.sqrt 2 * β * h1) (Real.sqrt 2 * β * h2) (cfg i))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [coe_combinedEquiv]
    rw [← hid z.1 z.2]
    linear_combination ((F z.1 - F z.2) * (G z.1 - G z.2))
      * vectorWeight_mul_eq_rot Gr A σ J h1 h2 β z.1 z.2
  rw [hkey]
  exact dRotInteraction_nonneg Gr hA hβJ hcα hcγ hobs

end IsingModel.ContinuousSpin
