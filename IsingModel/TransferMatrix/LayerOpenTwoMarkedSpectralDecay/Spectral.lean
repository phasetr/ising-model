import IsingModel.TransferMatrix.LayerOpenSlabGraph
import IsingModel.TransferMatrix.LayerOpenSpectral
import IsingModel.TransferMatrix.LayerOpenSpectralDenominator

/-!
# Finite open layer-slab two-marked spectral decay: spectral prefactor and sum bound

This is the spectral-coordinate child of
`IsingModel.TransferMatrix.LayerOpenTwoMarkedSpectralDecay`.  It collects the
`RealOrthogonalSpectralData` material: the two-marked spectral prefactor, the
central-channel cancellation lemmas, the boundary-vector two-marked product and
its spectral-sum expansion, and the resulting spectral-sum absolute bound.

See the umbrella module `LayerOpenTwoMarkedSpectralDecay` for the overview and
references.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace RealOrthogonalSpectralData

/-! ## Two-marked spectral prefactor -/

/-- The finite absolute coefficient prefactor for an open boundary-vector
two-marked spectral product.  The first mark `f` sits at the left cut and the
second mark `g` at the right cut. -/
noncomputable def boundaryTwoMarkedSpectralPrefactor {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f g vL vR : Ω → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ l,
    |E.boundaryCoordinates vL i * E.markedMatrix f i j *
      E.markedMatrix g j l * E.boundaryCoordinates vR l|

/-- The open boundary-vector two-marked spectral prefactor is nonnegative. -/
theorem boundaryTwoMarkedSpectralPrefactor_nonneg {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f g vL vR : Ω → ℝ) :
    0 ≤ E.boundaryTwoMarkedSpectralPrefactor f g vL vR := by
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun l _ => abs_nonneg _

/-- Taking the two marks equal recovers the single-mark spectral prefactor. -/
theorem boundaryTwoMarkedSpectralPrefactor_self {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f vL vR : Ω → ℝ) :
    E.boundaryTwoMarkedSpectralPrefactor f f vL vR =
      E.boundaryMarkedSpectralPrefactor f vL vR :=
  rfl

/-! ## Two-marked central-channel cancellation -/

/-- A top-supported left boundary vector and a zero dominant marked diagonal for
the *left* mark `f` give the central-channel cancellation for an open
two-marked boundary product.  The right mark `g` is unused: the left factor
already vanishes. -/
theorem boundaryTwoMarkedCentral_zero_of_topBoundary {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f g vL vR : Ω → ℝ) (top : Ω)
    (hL : ∀ i, i ≠ top → E.boundaryCoordinates vL i = 0)
    (hR : ∀ i, i ≠ top → E.boundaryCoordinates vR i = 0)
    (hG : E.markedMatrix f top top = 0) :
    ∀ i l,
      E.boundaryCoordinates vL i * E.markedMatrix f i top *
        E.markedMatrix g top l * E.boundaryCoordinates vR l = 0 := by
  intro i l
  by_cases hi : i = top
  · subst i
    by_cases hl : l = top
    · subst l
      simp [hG]
    · simp [hR l hl]
  · simp [hL i hi]

/-- If the left boundary vector is even, the *left* observable `f` is odd, the
top column is even, and every spectral-data column has a flip parity, then the
open central two-marked channel vanishes coefficientwise.  Only the left mark
matters; the right mark `g` is a passive spectator. -/
theorem boundaryTwoMarkedCentral_zero_of_equiv_evenBoundary_columnParity
    {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f g vL vR : Ω → ℝ)
    (top : Ω) (τ : Ω ≃ Ω)
    (hf_odd : ∀ x, f (τ x) = -f x)
    (hvL_even : ∀ x, vL (τ x) = vL x)
    (htop_even : E.ColumnFlipEven τ top)
    (hparity : E.ColumnFlipParity τ) :
    ∀ i l,
      E.boundaryCoordinates vL i * E.markedMatrix f i top *
        E.markedMatrix g top l * E.boundaryCoordinates vR l = 0 := by
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
        E.markedMatrix g top l * E.boundaryCoordinates vR l
        = (E.boundaryCoordinates vL i * E.markedMatrix f i top) *
            (E.markedMatrix g top l * E.boundaryCoordinates vR l) := by
          ring
    _ = 0 := by simp [hleft]

/-! ## Two-marked boundary product -/

/-- The finite boundary-vector two-marked product
`vLᵀ M^left diag(f) M^sep diag(g) M^right vR`. -/
noncomputable def boundaryTwoMarkedProduct
    (M : Matrix Ω Ω ℝ) (vL f g vR : Ω → ℝ)
    (left sep right : ℕ) : ℝ :=
  ∑ a, ∑ b,
    vL a * (M ^ left * Matrix.diagonal f * M ^ sep *
      Matrix.diagonal g * M ^ right) a b * vR b

/-- The boundary-vector two-marked product as a dot product. -/
theorem boundaryTwoMarkedProduct_eq_dotProduct
    (M : Matrix Ω Ω ℝ) (vL f g vR : Ω → ℝ)
    (left sep right : ℕ) :
    boundaryTwoMarkedProduct M vL f g vR left sep right =
      vL ⬝ᵥ ((M ^ left * Matrix.diagonal f * M ^ sep *
        Matrix.diagonal g * M ^ right) *ᵥ vR) := by
  unfold boundaryTwoMarkedProduct
  simp only [dotProduct, mulVec]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The two-diagonal boundary-vector power product expanded with two distinct
marked matrices `G` (left cut) and `K` (right cut). -/
theorem boundary_two_marked_diagonal_pow_eq_sum
    (G K : Matrix Ω Ω ℝ) (lam vL vR : Ω → ℝ)
    (left sep right : ℕ) :
    (∑ a, ∑ b,
      vL a * (Matrix.diagonal (fun i => lam i ^ left) * G *
        Matrix.diagonal (fun i => lam i ^ sep) * K *
        Matrix.diagonal (fun i => lam i ^ right)) a b * vR b)
      = ∑ i, ∑ j, ∑ l,
          vL i * lam i ^ left * G i j * lam j ^ sep *
          K j l * lam l ^ right * vR l := by
  apply Finset.sum_congr rfl
  intro i _
  calc
    ∑ b,
        vL i * (Matrix.diagonal (fun i => lam i ^ left) * G *
          Matrix.diagonal (fun i => lam i ^ sep) * K *
          Matrix.diagonal (fun i => lam i ^ right)) i b * vR b
        = ∑ l, ∑ j,
            vL i * lam i ^ left * G i j * lam j ^ sep *
            K j l * lam l ^ right * vR l := by
          apply Finset.sum_congr rfl
          intro l _
          rw [Matrix.mul_diagonal]
          rw [Matrix.mul_apply]
          rw [Finset.sum_mul]
          rw [Finset.mul_sum]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          rw [Matrix.mul_diagonal]
          rw [Matrix.diagonal_mul]
          ring
    _ = ∑ j, ∑ l,
            vL i * lam i ^ left * G i j * lam j ^ sep *
            K j l * lam l ^ right * vR l := by
          rw [Finset.sum_comm]

/-- A finite boundary-vector two-marked product written in explicit orthogonal
spectral coordinates. -/
theorem boundaryTwoMarkedProduct_eq_spectralSum {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (vL f g vR : Ω → ℝ)
    (left sep right : ℕ) :
    boundaryTwoMarkedProduct M vL f g vR left sep right =
      ∑ i, ∑ j, ∑ l,
        E.boundaryCoordinates vL i * E.eigenvalue i ^ left *
        E.markedMatrix f i j * E.eigenvalue j ^ sep *
        E.markedMatrix g j l * E.eigenvalue l ^ right *
        E.boundaryCoordinates vR l := by
  let Dleft : Matrix Ω Ω ℝ := Matrix.diagonal fun i => E.eigenvalue i ^ left
  let Dsep : Matrix Ω Ω ℝ := Matrix.diagonal fun i => E.eigenvalue i ^ sep
  let Dright : Matrix Ω Ω ℝ := Matrix.diagonal fun i => E.eigenvalue i ^ right
  let G : Matrix Ω Ω ℝ := E.markedMatrix f
  let K : Matrix Ω Ω ℝ := E.markedMatrix g
  let B : Matrix Ω Ω ℝ := Dleft * G * Dsep * K * Dright
  have hmat :
      M ^ left * Matrix.diagonal f * M ^ sep * Matrix.diagonal g * M ^ right =
        E.changeOfBasis * B * E.changeOfBasisᵀ := by
    dsimp [B, Dleft, Dsep, Dright, G, K]
    rw [E.pow_eq left, E.pow_eq sep, E.pow_eq right]
    unfold markedMatrix
    noncomm_ring [E.orthogonal_left]
  rw [boundaryTwoMarkedProduct_eq_dotProduct]
  rw [hmat]
  rw [dotProduct_mulVec]
  rw [← vecMul_vecMul vL (E.changeOfBasis * B) E.changeOfBasisᵀ]
  rw [← vecMul_vecMul vL E.changeOfBasis B]
  rw [← dotProduct_mulVec]
  have hleft :
      vL ᵥ* E.changeOfBasis = E.boundaryCoordinates vL := by
    ext i
    simp [vecMul, dotProduct, boundaryCoordinates]
  have hright :
      E.changeOfBasisᵀ *ᵥ vR = E.boundaryCoordinates vR := by
    ext i
    simp only [mulVec, dotProduct, Matrix.transpose_apply, boundaryCoordinates]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hleft, hright]
  dsimp [B, Dleft, Dsep, Dright, G, K]
  rw [← boundary_two_marked_diagonal_pow_eq_sum (E.markedMatrix f) (E.markedMatrix g)
    E.eigenvalue (E.boundaryCoordinates vL) (E.boundaryCoordinates vR) left sep right]
  simp only [dotProduct, vecMul]
  calc
    ∑ x,
        (∑ x_1,
          E.boundaryCoordinates vL x_1 *
            ((Matrix.diagonal (fun i => E.eigenvalue i ^ left) * E.markedMatrix f *
              Matrix.diagonal (fun i => E.eigenvalue i ^ sep) * E.markedMatrix g *
              Matrix.diagonal (fun i => E.eigenvalue i ^ right)) x_1 x)) *
          E.boundaryCoordinates vR x
        = ∑ x, ∑ x_1,
            E.boundaryCoordinates vL x_1 *
              ((Matrix.diagonal (fun i => E.eigenvalue i ^ left) * E.markedMatrix f *
                Matrix.diagonal (fun i => E.eigenvalue i ^ sep) * E.markedMatrix g *
                Matrix.diagonal (fun i => E.eigenvalue i ^ right)) x_1 x) *
              E.boundaryCoordinates vR x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
    _ = ∑ x_1, ∑ x,
            E.boundaryCoordinates vL x_1 *
              ((Matrix.diagonal (fun i => E.eigenvalue i ^ left) * E.markedMatrix f *
                Matrix.diagonal (fun i => E.eigenvalue i ^ sep) * E.markedMatrix g *
                Matrix.diagonal (fun i => E.eigenvalue i ^ right)) x_1 x) *
              E.boundaryCoordinates vR x := by
          rw [Finset.sum_comm]

/-! ## Two-marked spectral sum bound -/

/-- Spectral dominance and central-channel cancellation give an open
boundary-vector two-marked numerator bound in the separation exponent.  The
proof mirrors the single-mark `boundaryMarkedSpectralSum_abs_le_spectralPrefactor`
verbatim: the per-term estimate only splits on whether the middle index `j` is
`top`, and the right mark `g` enters only through the coefficient. -/
theorem boundaryTwoMarkedSpectralSum_abs_le_spectralPrefactor {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f g vL vR : Ω → ℝ)
    (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (eigenvalue_abs_le_scale : ∀ i, |E.eigenvalue i| ≤ scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (central_dominant_channel_zero : ∀ i l,
      E.boundaryCoordinates vL i * E.markedMatrix f i top *
        E.markedMatrix g top l * E.boundaryCoordinates vR l = 0)
    (left sep right : ℕ) :
    |∑ i, ∑ j, ∑ l,
        E.boundaryCoordinates vL i * E.eigenvalue i ^ left *
        E.markedMatrix f i j * E.eigenvalue j ^ sep *
        E.markedMatrix g j l * E.eigenvalue l ^ right *
        E.boundaryCoordinates vR l|
      ≤ E.boundaryTwoMarkedSpectralPrefactor f g vL vR *
          scale ^ (left + sep + right) * theta ^ sep := by
  let coeff : Ω → Ω → Ω → ℝ :=
    fun i j l =>
      E.boundaryCoordinates vL i * E.markedMatrix f i j *
        E.markedMatrix g j l * E.boundaryCoordinates vR l
  let term : Ω → Ω → Ω → ℝ :=
    fun i j l =>
      coeff i j l * E.eigenvalue i ^ left * E.eigenvalue j ^ sep *
        E.eigenvalue l ^ right
  have hscale_nonneg : 0 ≤ scale := scale_pos.le
  have htheta_scale_nonneg : 0 ≤ theta * scale :=
    mul_nonneg theta_nonneg hscale_nonneg
  have hsum :
      |∑ i, ∑ j, ∑ l, term i j l| ≤ ∑ i, ∑ j, ∑ l, |term i j l| := by
    calc
      |∑ i, ∑ j, ∑ l, term i j l|
          ≤ ∑ i, |∑ j, ∑ l, term i j l| :=
            Finset.abs_sum_le_sum_abs (fun i => ∑ j, ∑ l, term i j l) Finset.univ
      _ ≤ ∑ i, ∑ j, |∑ l, term i j l| := by
            exact Finset.sum_le_sum fun i _ =>
              Finset.abs_sum_le_sum_abs (fun j => ∑ l, term i j l) Finset.univ
      _ ≤ ∑ i, ∑ j, ∑ l, |term i j l| := by
            exact Finset.sum_le_sum fun i _ =>
              Finset.sum_le_sum fun j _ =>
                Finset.abs_sum_le_sum_abs (fun l => term i j l) Finset.univ
  have hterm : ∀ i j l, |term i j l| ≤
      |coeff i j l| * (scale ^ (left + sep + right) * theta ^ sep) := by
    intro i j l
    by_cases hj : j = top
    · subst j
      have hcoeff : coeff i top l = 0 := central_dominant_channel_zero i l
      simp [term, hcoeff]
    · have hipow : |E.eigenvalue i| ^ left ≤ scale ^ left :=
        pow_le_pow_left₀ (abs_nonneg _) (eigenvalue_abs_le_scale i) left
      have hjpow : |E.eigenvalue j| ^ sep ≤ (theta * scale) ^ sep :=
        pow_le_pow_left₀ (abs_nonneg _) (subdominant_abs_le j hj) sep
      have hlpow : |E.eigenvalue l| ^ right ≤ scale ^ right :=
        pow_le_pow_left₀ (abs_nonneg _) (eigenvalue_abs_le_scale l) right
      have hpow_mul :
          |E.eigenvalue i| ^ left * |E.eigenvalue j| ^ sep *
              |E.eigenvalue l| ^ right
            ≤ scale ^ left * (theta * scale) ^ sep * scale ^ right := by
        exact mul_le_mul
          (mul_le_mul hipow hjpow (pow_nonneg (abs_nonneg _) sep)
            (pow_nonneg hscale_nonneg left))
          hlpow (pow_nonneg (abs_nonneg _) right)
          (mul_nonneg (pow_nonneg hscale_nonneg left)
            (pow_nonneg htheta_scale_nonneg sep))
      have hpow_eq :
          scale ^ left * (theta * scale) ^ sep * scale ^ right =
            scale ^ (left + sep + right) * theta ^ sep := by
        rw [mul_pow, pow_add, pow_add]
        ring
      calc
        |term i j l|
            = |coeff i j l| *
                (|E.eigenvalue i| ^ left * |E.eigenvalue j| ^ sep *
                  |E.eigenvalue l| ^ right) := by
              simp [term, abs_mul, abs_pow, mul_assoc]
        _ ≤ |coeff i j l| *
              (scale ^ left * (theta * scale) ^ sep * scale ^ right) :=
                mul_le_mul_of_nonneg_left hpow_mul (abs_nonneg _)
        _ = |coeff i j l| * (scale ^ (left + sep + right) * theta ^ sep) := by
              rw [hpow_eq]
  calc
    |∑ i, ∑ j, ∑ l,
        E.boundaryCoordinates vL i * E.eigenvalue i ^ left *
        E.markedMatrix f i j * E.eigenvalue j ^ sep *
        E.markedMatrix g j l * E.eigenvalue l ^ right *
        E.boundaryCoordinates vR l|
        = |∑ i, ∑ j, ∑ l, term i j l| := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro l _
            simp [term, coeff]
            ring
    _ ≤ ∑ i, ∑ j, ∑ l, |term i j l| := hsum
    _ ≤ ∑ i, ∑ j, ∑ l,
          |coeff i j l| * (scale ^ (left + sep + right) * theta ^ sep) := by
            exact Finset.sum_le_sum fun i _ =>
              Finset.sum_le_sum fun j _ =>
                Finset.sum_le_sum fun l _ => hterm i j l
    _ = E.boundaryTwoMarkedSpectralPrefactor f g vL vR *
          scale ^ (left + sep + right) * theta ^ sep := by
            simp [boundaryTwoMarkedSpectralPrefactor, coeff, Finset.sum_mul, mul_assoc]

end RealOrthogonalSpectralData

end TransferMatrix

end IsingModel
