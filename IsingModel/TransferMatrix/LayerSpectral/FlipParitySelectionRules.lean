import IsingModel.TransferMatrix.LayerSpectral.HermitianBridge

/-!
# Flip-parity selection rules (GJ §17.1)

Parity (flip-even / flip-odd) selection rules for the real orthogonal spectral
data, the induced marked-matrix and boundary vanishing.  Child module of the
`LayerSpectral.FlipParity` scaffold.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace RealOrthogonalSpectralData

/-! ## Flip-parity selection rules -/

/-- A spectral-data column is even under an involutive relabelling. -/
def ColumnFlipEven {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (τ : Ω ≃ Ω) (i : Ω) : Prop :=
  ∀ x, E.changeOfBasis (τ x) i = E.changeOfBasis x i

/-- A spectral-data column is odd under an involutive relabelling. -/
def ColumnFlipOdd {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (τ : Ω ≃ Ω) (i : Ω) : Prop :=
  ∀ x, E.changeOfBasis (τ x) i = -E.changeOfBasis x i

/-- A spectral basis is adapted to a two-sector flip parity when every column
is either even or odd under the relabelling. -/
def ColumnFlipParity {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (τ : Ω ≃ Ω) : Prop :=
  ∀ i, E.ColumnFlipEven τ i ∨ E.ColumnFlipOdd τ i

/-- An even boundary vector has zero coordinate against an odd spectral-data
column. -/
theorem boundaryCoordinates_zero_of_equiv_even_odd {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (i : Ω) (τ : Ω ≃ Ω)
    (hv_even : ∀ x, v (τ x) = v x)
    (hcol_odd : E.ColumnFlipOdd τ i) :
    E.boundaryCoordinates v i = 0 := by
  rw [boundaryCoordinates]
  let term : Ω → ℝ := fun x => v x * E.changeOfBasis x i
  change (∑ x : Ω, term x) = 0
  have hflip : ∀ x : Ω, term (τ x) = -term x := by
    intro x
    simp [term, hv_even x, hcol_odd x]
  have hsum_flip : (∑ x : Ω, term (τ x)) = ∑ x : Ω, term x :=
    Equiv.sum_comp τ term
  have hself_neg : (∑ x : Ω, term x) = -∑ x : Ω, term x := by
    calc
      (∑ x : Ω, term x) = ∑ x : Ω, term (τ x) := hsum_flip.symm
      _ = ∑ x : Ω, -term x := by simp_rw [hflip]
      _ = -∑ x : Ω, term x := by rw [Finset.sum_neg_distrib]
  linarith

/-- An odd observable has zero marked-matrix entry between two even
spectral-data columns. -/
theorem markedMatrix_zero_of_equiv_odd_even_even {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) (i j : Ω) (τ : Ω ≃ Ω)
    (hf_odd : ∀ x, f (τ x) = -f x)
    (hi_even : E.ColumnFlipEven τ i) (hj_even : E.ColumnFlipEven τ j) :
    E.markedMatrix f i j = 0 := by
  rw [E.markedMatrix_apply f i j]
  let term : Ω → ℝ :=
    fun x => E.changeOfBasis x i * f x * E.changeOfBasis x j
  change (∑ x : Ω, term x) = 0
  have hflip : ∀ x : Ω, term (τ x) = -term x := by
    intro x
    simp [term, hf_odd x, hi_even x, hj_even x]
  have hsum_flip : (∑ x : Ω, term (τ x)) = ∑ x : Ω, term x :=
    Equiv.sum_comp τ term
  have hself_neg : (∑ x : Ω, term x) = -∑ x : Ω, term x := by
    calc
      (∑ x : Ω, term x) = ∑ x : Ω, term (τ x) := hsum_flip.symm
      _ = ∑ x : Ω, -term x := by simp_rw [hflip]
      _ = -∑ x : Ω, term x := by rw [Finset.sum_neg_distrib]
  linarith

/-- An odd observable has zero marked-matrix entry between two odd
spectral-data columns. -/
theorem markedMatrix_zero_of_equiv_odd_odd_odd {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) (i j : Ω) (τ : Ω ≃ Ω)
    (hf_odd : ∀ x, f (τ x) = -f x)
    (hi_odd : E.ColumnFlipOdd τ i) (hj_odd : E.ColumnFlipOdd τ j) :
    E.markedMatrix f i j = 0 := by
  rw [E.markedMatrix_apply f i j]
  let term : Ω → ℝ :=
    fun x => E.changeOfBasis x i * f x * E.changeOfBasis x j
  change (∑ x : Ω, term x) = 0
  have hflip : ∀ x : Ω, term (τ x) = -term x := by
    intro x
    simp [term, hf_odd x, hi_odd x, hj_odd x]
  have hsum_flip : (∑ x : Ω, term (τ x)) = ∑ x : Ω, term x :=
    Equiv.sum_comp τ term
  have hself_neg : (∑ x : Ω, term x) = -∑ x : Ω, term x := by
    calc
      (∑ x : Ω, term x) = ∑ x : Ω, term (τ x) := hsum_flip.symm
      _ = ∑ x : Ω, -term x := by simp_rw [hflip]
      _ = -∑ x : Ω, term x := by rw [Finset.sum_neg_distrib]
  linarith

/-- If the left boundary vector is even, the observable is odd, the top column
is even, and every spectral-data column has a flip parity, then the open
central marked channel vanishes coefficientwise. -/
theorem boundaryMarkedCentral_zero_of_equiv_evenBoundary_columnParity
    {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f vL vR : Ω → ℝ)
    (top : Ω) (τ : Ω ≃ Ω)
    (hf_odd : ∀ x, f (τ x) = -f x)
    (hvL_even : ∀ x, vL (τ x) = vL x)
    (htop_even : E.ColumnFlipEven τ top)
    (hparity : E.ColumnFlipParity τ) :
    ∀ i l,
      E.boundaryCoordinates vL i * E.markedMatrix f i top *
        E.markedMatrix f top l * E.boundaryCoordinates vR l = 0 := by
  intro i l
  have hleft :
      E.boundaryCoordinates vL i * E.markedMatrix f i top = 0 := by
    rcases hparity i with hi_even | hi_odd
    · have hmarked :
          E.markedMatrix f i top = 0 :=
        E.markedMatrix_zero_of_equiv_odd_even_even f i top τ
          hf_odd hi_even htop_even
      simp [hmarked]
    · have hboundary :
          E.boundaryCoordinates vL i = 0 :=
        E.boundaryCoordinates_zero_of_equiv_even_odd vL i τ hvL_even hi_odd
      simp [hboundary]
  calc
    E.boundaryCoordinates vL i * E.markedMatrix f i top *
        E.markedMatrix f top l * E.boundaryCoordinates vR l
        = (E.boundaryCoordinates vL i * E.markedMatrix f i top) *
            (E.markedMatrix f top l * E.boundaryCoordinates vR l) := by
          ring
    _ = 0 := by simp [hleft]

end RealOrthogonalSpectralData

end TransferMatrix

end IsingModel
