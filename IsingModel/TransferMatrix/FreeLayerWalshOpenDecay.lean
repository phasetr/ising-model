import IsingModel.TransferMatrix.FreeLayerWalshOpenPerron
import IsingModel.TransferMatrix.OneDimCorrelationLength

/-!
# Sharp finite free-layer open Walsh decay

This file removes the remaining finite open-boundary Walsh prefactor from the
zero-field free-layer open-slab estimate.  In the free Walsh basis, the open
boundary vector has only the top coordinate, and a single-site spin insertion
maps the top Walsh column to the singleton Walsh column.  Consequently the
open marked prefactor and denominator prefactor agree, so the finite
same-transverse-site open-slab bound has coefficient `1`.

The results are finite and free-layer only.  They do not assert an interacting
transverse-layer spectral window, a thermodynamic limit, or final hyperplane
exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators
open Matrix

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## Singleton Walsh column and marked matrix coefficients -/

/-- The Walsh index whose down-spin set is the singleton `{x}`. -/
def freeLayerWalshSingleton (x : S) : LayerState S :=
  layerStateDownSetEquivFinset.symm {x}

/-- The singleton Walsh index has down-spin set `{x}`. -/
@[simp]
theorem layerStateDownSet_freeLayerWalshSingleton (x : S) :
    layerStateDownSet (freeLayerWalshSingleton (S := S) x) = {x} := by
  exact layerStateDownSetEquivFinset.right_inv {x}

omit [Fintype S] [DecidableEq S] in
/-- A fixed-site layer spin is the singleton spin product. -/
@[simp]
theorem layerSpinAt_eq_spinProduct_singleton (x : S) :
    layerSpinAt x = spinProduct ({x} : Finset S) := by
  funext ω
  simp [layerSpinAt, spinProduct, Spin.sign]

/-- Multiplication by the fixed-site spin sends the Walsh top column to the
singleton Walsh column. -/
theorem freeLayerPhysical_top_column_mul_layerSpinAt
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S) (ω : LayerState S) :
    (freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).changeOfBasis
        ω (freeLayerWalshTop (S := S)) * layerSpinAt x ω =
      (freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).changeOfBasis
        ω (freeLayerWalshSingleton (S := S) x) := by
  change
    freeLayerWalshMatrix (S := S) ω (freeLayerWalshTop (S := S)) *
        layerSpinAt x ω =
      freeLayerWalshMatrix (S := S) ω (freeLayerWalshSingleton (S := S) x)
  unfold freeLayerWalshMatrix freeLayerWalshColumn
  rw [layerStateDownSet_freeLayerWalshTop,
    layerStateDownSet_freeLayerWalshSingleton]
  simp only [layerSpinAt_eq_spinProduct_singleton, spinProduct_empty,
    spinProduct_singleton]
  ring

/-- The Walsh marked matrix for a single-site spin maps the top mode to the
singleton mode and vanishes on all other target modes. -/
theorem freeLayerPhysical_markedMatrix_layerSpinAt_top_eq_ite
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S) (i : LayerState S) :
    (freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).markedMatrix
        (layerSpinAt x) (freeLayerWalshTop (S := S)) i =
      if layerStateDownSet i = ({x} : Finset S) then 1 else 0 := by
  classical
  let E := freeLayerPhysicalOrthogonalSpectralData (S := S) p hp
  let top : LayerState S := freeLayerWalshTop (S := S)
  let sing : LayerState S := freeLayerWalshSingleton (S := S) x
  calc
    E.markedMatrix (layerSpinAt x) top i
        = ∑ ω : LayerState S,
            E.changeOfBasis ω top * layerSpinAt x ω * E.changeOfBasis ω i := by
          rw [RealOrthogonalSpectralData.markedMatrix_apply]
    _ = ∑ ω : LayerState S,
            E.changeOfBasis ω sing * E.changeOfBasis ω i := by
          refine Finset.sum_congr rfl ?_
          intro ω _hω
          rw [← freeLayerPhysical_top_column_mul_layerSpinAt (S := S) p hp x ω]
    _ = (E.changeOfBasisᵀ * E.changeOfBasis) sing i := by
          simp [Matrix.mul_apply]
    _ = (1 : Matrix (LayerState S) (LayerState S) ℝ) sing i := by
          rw [E.orthogonal_left]
    _ = if layerStateDownSet i = ({x} : Finset S) then 1 else 0 := by
          by_cases hi : layerStateDownSet i = ({x} : Finset S)
          · have hsing : sing = i := by
              apply layerStateDownSetEquivFinset.injective
              change layerStateDownSet sing = layerStateDownSet i
              rw [show layerStateDownSet sing = ({x} : Finset S) by simp [sing]]
              exact hi.symm
            rw [hsing]
            simp [hi]
          · have hsing : sing ≠ i := by
              intro h
              apply hi
              rw [← h]
              simp [sing]
            simp [hsing, hi]

/-- Symmetric form of the single-site Walsh marked-matrix top coefficient. -/
theorem freeLayerPhysical_markedMatrix_layerSpinAt_eq_ite_top
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S) (i : LayerState S) :
    (freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).markedMatrix
        (layerSpinAt x) i (freeLayerWalshTop (S := S)) =
      if layerStateDownSet i = ({x} : Finset S) then 1 else 0 := by
  rw [(freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).markedMatrix_comm]
  exact freeLayerPhysical_markedMatrix_layerSpinAt_top_eq_ite (S := S) p hp x i

/-! ## Open free-layer prefactor collapse -/

/-- The free open boundary denominator prefactor is the square of the top
boundary coordinate because every non-top boundary coordinate vanishes. -/
theorem freeLayerPhysical_boundarySpectralPartitionPrefactor_eq_top_sq
    (p : IsingParams ℝ) (hp : p.h = 0) (theta : ℝ) :
    (freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).boundarySpectralPartitionPrefactor
        (layerOpenBalancedBoundaryVector
          (layerInternalWeight (⊥ : SimpleGraph S) p))
        (freeLayerWalshTop (S := S)) theta =
      ((freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).boundaryCoordinates
        (layerOpenBalancedBoundaryVector
          (layerInternalWeight (⊥ : SimpleGraph S) p))
        (freeLayerWalshTop (S := S))) ^ 2 := by
  classical
  let E := freeLayerPhysicalOrthogonalSpectralData (S := S) p hp
  let v := layerOpenBalancedBoundaryVector
    (layerInternalWeight (⊥ : SimpleGraph S) p)
  let top : LayerState S := freeLayerWalshTop (S := S)
  have hsum_zero :
      ∑ i ∈ Finset.univ.erase top, (E.boundaryCoordinates v i) ^ 2 = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi_ne : i ≠ top := (Finset.mem_erase.mp hi).1
    rw [freeLayerPhysical_boundaryCoordinates_nonTop_zero (S := S) p hp hi_ne]
    ring
  simp [RealOrthogonalSpectralData.boundarySpectralPartitionPrefactor, E, v, top,
    hsum_zero]

/-- In the zero-field free layer, the open marked Walsh prefactor for a
single-site insertion equals the square of the top boundary coordinate. -/
theorem freeLayerPhysical_boundaryMarkedSpectralPrefactor_eq_top_sq
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S) :
    (freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).boundaryMarkedSpectralPrefactor
        (layerSpinAt x)
        (layerOpenBalancedBoundaryVector
          (layerInternalWeight (⊥ : SimpleGraph S) p))
        (layerOpenBalancedBoundaryVector
          (layerInternalWeight (⊥ : SimpleGraph S) p)) =
      ((freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).boundaryCoordinates
        (layerOpenBalancedBoundaryVector
          (layerInternalWeight (⊥ : SimpleGraph S) p))
        (freeLayerWalshTop (S := S))) ^ 2 := by
  classical
  let E := freeLayerPhysicalOrthogonalSpectralData (S := S) p hp
  let v := layerOpenBalancedBoundaryVector
    (layerInternalWeight (⊥ : SimpleGraph S) p)
  let top : LayerState S := freeLayerWalshTop (S := S)
  let sing : LayerState S := freeLayerWalshSingleton (S := S) x
  have hcoord_ne : ∀ i, i ≠ top → E.boundaryCoordinates v i = 0 := by
    intro i hi
    have hi' : i ≠ freeLayerWalshTop (S := S) := by
      simpa [top] using hi
    simpa [E, v] using
      freeLayerPhysical_boundaryCoordinates_nonTop_zero (S := S) p hp hi'
  have htop_right :
      ∀ j, E.markedMatrix (layerSpinAt x) top j =
        if j = sing then 1 else 0 := by
    intro j
    rw [freeLayerPhysical_markedMatrix_layerSpinAt_top_eq_ite (S := S) p hp x j]
    by_cases hj : j = sing
    · simp [hj, sing]
    · have hdown : layerStateDownSet j ≠ ({x} : Finset S) := by
        intro h
        apply hj
        symm
        apply layerStateDownSetEquivFinset.injective
        change layerStateDownSet sing = layerStateDownSet j
        rw [show layerStateDownSet sing = ({x} : Finset S) by simp [sing]]
        exact h.symm
      simp [hj, hdown]
  have htop_left :
      ∀ j, E.markedMatrix (layerSpinAt x) j top =
        if j = sing then 1 else 0 := by
    intro j
    rw [freeLayerPhysical_markedMatrix_layerSpinAt_eq_ite_top (S := S) p hp x j]
    by_cases hj : j = sing
    · simp [hj, sing]
    · have hdown : layerStateDownSet j ≠ ({x} : Finset S) := by
        intro h
        apply hj
        symm
        apply layerStateDownSetEquivFinset.injective
        change layerStateDownSet sing = layerStateDownSet j
        rw [show layerStateDownSet sing = ({x} : Finset S) by simp [sing]]
        exact h.symm
      simp [hj, hdown]
  rw [RealOrthogonalSpectralData.boundaryMarkedSpectralPrefactor]
  calc
    ∑ i, ∑ j, ∑ l,
        |E.boundaryCoordinates v i * E.markedMatrix (layerSpinAt x) i j *
          E.markedMatrix (layerSpinAt x) j l * E.boundaryCoordinates v l|
        = ∑ j, ∑ l,
            |E.boundaryCoordinates v top * E.markedMatrix (layerSpinAt x) top j *
              E.markedMatrix (layerSpinAt x) j l * E.boundaryCoordinates v l| := by
          refine Finset.sum_eq_single top ?_ ?_
          · intro i _hi hi_ne
            rw [hcoord_ne i hi_ne]
            simp
          · intro htop_not_mem
            simp at htop_not_mem
    _ = ∑ j,
            |E.boundaryCoordinates v top * E.markedMatrix (layerSpinAt x) top j *
              E.markedMatrix (layerSpinAt x) j top * E.boundaryCoordinates v top| := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          refine Finset.sum_eq_single top ?_ ?_
          · intro l _hl hl_ne
            rw [hcoord_ne l hl_ne]
            simp
          · intro htop_not_mem
            simp at htop_not_mem
    _ = |E.boundaryCoordinates v top * E.markedMatrix (layerSpinAt x) top sing *
            E.markedMatrix (layerSpinAt x) sing top * E.boundaryCoordinates v top| := by
          refine Finset.sum_eq_single sing ?_ ?_
          · intro j _hj hj_ne
            rw [htop_right j]
            simp [hj_ne]
          · intro hsing_not_mem
            simp at hsing_not_mem
    _ = (E.boundaryCoordinates v top) ^ 2 := by
          rw [htop_right sing, htop_left sing]
          simp
          ring

/-- The zero-field free-layer open Walsh prefactor ratio is exactly `1`. -/
theorem freeLayerPhysical_openPrefactorRatio_eq_one
    (p : IsingParams ℝ) (hp : p.h = 0) (x : S) (theta : ℝ) :
    (freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).boundaryMarkedSpectralPrefactor
          (layerSpinAt x)
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (⊥ : SimpleGraph S) p))
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (⊥ : SimpleGraph S) p)) /
        (freeLayerPhysicalOrthogonalSpectralData (S := S) p hp).boundarySpectralPartitionPrefactor
          (layerOpenBalancedBoundaryVector
            (layerInternalWeight (⊥ : SimpleGraph S) p))
          (freeLayerWalshTop (S := S)) theta =
      1 := by
  let E := freeLayerPhysicalOrthogonalSpectralData (S := S) p hp
  let v := layerOpenBalancedBoundaryVector
    (layerInternalWeight (⊥ : SimpleGraph S) p)
  let top : LayerState S := freeLayerWalshTop (S := S)
  have hnum :
      E.boundaryMarkedSpectralPrefactor (layerSpinAt x) v v =
        (E.boundaryCoordinates v top) ^ 2 := by
    simpa [E, v, top] using
      freeLayerPhysical_boundaryMarkedSpectralPrefactor_eq_top_sq (S := S) p hp x
  have hden :
      E.boundarySpectralPartitionPrefactor v top theta =
        (E.boundaryCoordinates v top) ^ 2 := by
    simpa [E, v, top] using
      freeLayerPhysical_boundarySpectralPartitionPrefactor_eq_top_sq
        (S := S) p hp theta
  have hpos : 0 < (E.boundaryCoordinates v top) ^ 2 := by
    simpa [E, v, top] using
      layerOpenBoundaryCoordinate_sq_pos_of_signedPositiveColumn
        (layerInternalWeight (⊥ : SimpleGraph S) p)
        (fun _ => Real.exp_pos _)
        (freeLayerPhysicalOrthogonalSpectralData (S := S) p hp)
        (freeLayerWalshTop (S := S))
        (freeLayerPhysicalOrthogonalSpectralData_top_signedPositiveColumn
          (S := S) p hp)
  rw [hnum, hden]
  exact div_self (ne_of_gt hpos)

/-! ## Clean finite free-layer open decay -/

/-- Project-level finite open-slab same-transverse-site correlation decay for
the zero-field free layer with the sharp coefficient `1`. -/
theorem correlation_freeLayerOpenSlabGraph_same_transverse_abs_le_tanh_clean
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J) (x : S)
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation
      (layerOpenSlabGraph (S := S) (⊥ : SimpleGraph S)
        (layerIdentityTransitionPairs S) (left + sep + right)) p
      ({Prod.mk (layerOpenLeftIndex left sep right) x,
        Prod.mk (layerOpenRightIndex left sep right) x} :
          Finset (LayerOpenSlabSite (left + sep + right) S))|
      ≤ Real.tanh (p.β * p.J) ^ sep := by
  have hraw :=
    correlation_freeLayerOpenSlabGraph_same_transverse_abs_le_tanh
      (S := S) p hp hβJ x left sep right hsep
  have hratio :=
    freeLayerPhysical_openPrefactorRatio_eq_one
      (S := S) p hp x (Real.tanh (p.β * p.J))
  rw [hratio, one_mul] at hraw
  exact hraw

/-- Mass-form version of the sharp finite free-layer open decay bound. -/
theorem correlation_freeLayerOpenSlabGraph_same_transverse_abs_le_exp_neg_mass
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J) (x : S)
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation
      (layerOpenSlabGraph (S := S) (⊥ : SimpleGraph S)
        (layerIdentityTransitionPairs S) (left + sep + right)) p
      ({Prod.mk (layerOpenLeftIndex left sep right) x,
        Prod.mk (layerOpenRightIndex left sep right) x} :
          Finset (LayerOpenSlabSite (left + sep + right) S))|
      ≤ Real.exp (-(correlationMass (p.β * p.J)) * sep) := by
  rw [← tanh_pow_eq_exp_neg_mass hβJ sep]
  exact
    correlation_freeLayerOpenSlabGraph_same_transverse_abs_le_tanh_clean
      (S := S) p hp hβJ x left sep right hsep

end TransferMatrix

end IsingModel
