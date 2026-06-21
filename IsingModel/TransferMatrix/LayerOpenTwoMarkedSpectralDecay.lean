import IsingModel.TransferMatrix.LayerOpenSlabGraph
import IsingModel.TransferMatrix.LayerOpenSpectral
import IsingModel.TransferMatrix.LayerOpenSpectralDecay

/-!
# Finite open layer-slab two-marked spectral decay (GJ Section 17.1)

This file generalises the single-mark open-slab spectral decay to *two distinct
marks* `f`, `g` at the two observable cut points.  The single-mark chain inserts
the same observable `f` at the left (`i`--`j`) and right (`j`--`l`) spectral cut;
here the left cut carries `f` and the right cut carries `g`.  This is exactly the
shape needed to bound cross-transverse-site correlations
`⟨σ_(left,x) · σ_(left+sep,y)⟩` with `x ≠ y`, where the first mark is
`layerSpinAt x` and the second mark is `layerSpinAt y`.

The bulk of the single-mark glue is mark-agnostic (the path-glue combinatorics
and the denominator/partition infrastructure carry over verbatim), so only the
genuinely two-mark numerator pieces are twinned here.  The central-channel
cancellation still only needs the *left* mark to kill the dominant marked
diagonal; the right mark is a passive spectator.

The statements remain finite and conditional.  They do not prove an open
Perron--Frobenius input, a physical interacting spectral window,
thermodynamic-limit decay, or final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
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

/-! ## Two-marked open numerator chain -/

/-- A pure reindexing of a seven-fold finite sum, used to expand the two-marked
matrix-power numerator into glued open paths.  This is a non-private copy of the
single-mark `sum_reorder_7` helper. -/
private theorem two_marked_sum_reorder_7 {A B C D E F G R : Type*} [Fintype A]
    [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype F] [Fintype G]
    [AddCommMonoid R]
    (H : A → B → C → D → E → F → G → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, ∑ g, H a b c d e f g)
      = ∑ g, ∑ f, ∑ e, ∑ a, ∑ b, ∑ c, ∑ d, H a b c d e f g := by
  let e : A × B × C × D × E × F × G ≃ G × F × E × A × B × C × D := {
    toFun := fun p =>
      (p.2.2.2.2.2.2, p.2.2.2.2.2.1, p.2.2.2.2.1, p.1, p.2.1, p.2.2.1,
        p.2.2.2.1)
    invFun := fun q =>
      (q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2.1, q.2.2.2.2.2.2, q.2.2.1,
        q.2.1, q.1)
    left_inv := by intro p; ext <;> simp
    right_inv := by intro q; ext <;> simp }
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, ∑ g, H a b c d e f g)
        = ∑ p : A × B × C × D × E × F × G,
            H p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
              p.2.2.2.2.2.2 := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl; intro a _
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl; intro b _
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl; intro c _
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl; intro d _
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl; intro e _
          rw [Fintype.sum_prod_type]
    _ = ∑ q : G × F × E × A × B × C × D,
            H q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2 q.2.2.1
              q.2.1 q.1 := by
          exact Equiv.sum_comp e (fun q : G × F × E × A × B × C × D =>
            H q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2 q.2.2.1
              q.2.1 q.1)
    _ = ∑ g, ∑ f, ∑ e, ∑ a, ∑ b, ∑ c, ∑ d, H a b c d e f g := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl; intro g _
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl; intro f _
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl; intro e _
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl; intro a _
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl; intro b _
          rw [Fintype.sum_prod_type]

/-- The finite open two-marked numerator as the boundary-vector matrix product
`u^T T^left D_f T^sep D_g T^right 1`, before expanding into endpoint sums. -/
noncomputable def layerOpenTwoMarkedMatrixProductNumerator
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f g : Ω → ℝ)
    (left sep right : ℕ) : ℝ :=
  let M := layerTransferMatrix u k
  ∑ a : Ω, ∑ b : Ω,
    u a * (M ^ left * Matrix.diagonal f * M ^ sep * Matrix.diagonal g * M ^ right) a b

/-- The finite open two-marked numerator matrix-power expression expanded as a
four-endpoint sum. -/
noncomputable def layerOpenTwoMarkedMatrixPowerNumerator
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f g : Ω → ℝ)
    (left sep right : ℕ) : ℝ :=
  let M := layerTransferMatrix u k
  ∑ a : Ω, ∑ x : Ω, ∑ y : Ω, ∑ b : Ω,
    u a * f x * g y * (M ^ left) a x * (M ^ sep) x y * (M ^ right) y b

/-- The three-open-path expansion of an open two-marked matrix-power numerator,
with distinct marks `d` (left cut) and `e` (right cut). -/
noncomputable def openTwoMarkedPathTripleNumerator
    (M : Matrix Ω Ω ℝ) (w d e : Ω → ℝ)
    (left sep right : ℕ) : ℝ :=
  ∑ σ : Fin (left + 1) → Ω,
  ∑ τ : Fin (sep + 1) → Ω,
  ∑ ρ : Fin (right + 1) → Ω,
    if σ (Fin.last left) = τ 0 ∧ τ (Fin.last sep) = ρ 0 then
      w (σ 0) * d (σ (Fin.last left)) * e (τ (Fin.last sep)) *
        pathWeight M σ * pathWeight M τ * pathWeight M ρ
    else 0

/-- The unnormalised open two-marked numerator, as a transfer-matrix open-path
sum.  The left observable `f` sits at the left endpoint and `g` at the right
endpoint. -/
def layerOpenTwoMarkedTransferTwoPointNumerator
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f g : Ω → ℝ)
    (left sep right : ℕ) : ℝ :=
  ∑ c : Fin (left + sep + right + 1) → Ω,
    f (c (layerOpenLeftIndex left sep right))
      * g (c (layerOpenRightIndex left sep right))
      * (u (c 0) * pathWeight (layerTransferMatrix u k) c)

/-- The three-path open two-marked numerator is the same finite sum as the single
open-path transfer numerator with two distinct marked positions. -/
theorem openTwoMarkedPathTripleNumerator_eq_singlePathSum
    (M : Matrix Ω Ω ℝ) (w d e : Ω → ℝ)
    (left sep right : ℕ) :
    openTwoMarkedPathTripleNumerator M w d e left sep right =
      ∑ c : Fin (left + sep + right + 1) → Ω,
        d (c (layerOpenLeftIndex left sep right))
          * e (c (layerOpenRightIndex left sep right))
          * (w (c 0) * pathWeight M c) := by
  unfold openTwoMarkedPathTripleNumerator
  rw [← Finset.sum_product', ← Finset.sum_product', ← Finset.sum_filter]
  refine Finset.sum_bij'
    (fun (p : ((Fin (left + 1) → Ω) × (Fin (sep + 1) → Ω)) ×
        (Fin (right + 1) → Ω)) _ =>
      openMarkedTripleGlue p.1.1 p.1.2 p.2)
    (fun c _ =>
      ((openMarkedTripleLeft c, openMarkedTripleMiddle c), openMarkedTripleRight c))
    ?_ ?_ ?_ ?_ ?_
  · intro p _
    exact Finset.mem_univ _
  · intro c _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact ⟨openMarkedTripleLeft_last_eq_middle_zero c,
      openMarkedTripleMiddle_last_eq_right_zero c⟩
  · intro p hp
    dsimp only
    obtain ⟨hστ, hτρ⟩ := (Finset.mem_filter.mp hp).2
    exact Prod.ext
      (Prod.ext
        (openMarkedTripleLeft_glue p.1.1 p.1.2 p.2)
        (openMarkedTripleMiddle_glue p.1.1 p.1.2 p.2 hστ))
      (openMarkedTripleRight_glue p.1.1 p.1.2 p.2 hστ hτρ)
  · intro c _
    exact openMarkedTripleGlue_split c
  · intro p hp
    dsimp only
    obtain ⟨hστ, hτρ⟩ := (Finset.mem_filter.mp hp).2
    rw [openMarkedTripleGlue_apply_zero, openMarkedTripleGlue_apply_left,
      openMarkedTripleGlue_apply_right _ _ _ hστ,
      pathWeight_openMarkedTripleGlue M _ _ _ hστ hτρ]
    ring

/-- The four-endpoint matrix-power sum expands to the three glued open-path sum
for two distinct marks. -/
theorem openTwoMarkedMatrixPowerSum_eq_pathTripleNumerator
    (M : Matrix Ω Ω ℝ) (w d e : Ω → ℝ)
    (left sep right : ℕ) :
    (∑ a : Ω, ∑ x : Ω, ∑ y : Ω, ∑ b : Ω,
      w a * d x * e y * (M ^ left) a x * (M ^ sep) x y * (M ^ right) y b) =
      openTwoMarkedPathTripleNumerator M w d e left sep right := by
  unfold openTwoMarkedPathTripleNumerator
  simp_rw [pow_apply_eq_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [two_marked_sum_reorder_7 (A := Ω) (B := Ω) (C := Ω) (D := Ω)
    (E := Fin (right + 1) → Ω) (F := Fin (sep + 1) → Ω) (G := Fin (left + 1) → Ω)
    (H := fun a x y b ρ τ σ =>
      ((w a * d x * e y *
        (if σ 0 = a ∧ σ (Fin.last left) = x then pathWeight M σ else 0)) *
        (if τ 0 = x ∧ τ (Fin.last sep) = y then pathWeight M τ else 0)) *
        (if ρ 0 = y ∧ ρ (Fin.last right) = b then pathWeight M ρ else 0))]
  refine Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun τ _ =>
    Finset.sum_congr rfl (fun ρ _ => ?_)))
  rw [Finset.sum_eq_single (σ 0)]
  · rw [Finset.sum_eq_single (σ (Fin.last left))]
    · rw [Finset.sum_eq_single (τ (Fin.last sep))]
      · rw [Finset.sum_eq_single (ρ (Fin.last right))]
        · by_cases h1 : σ (Fin.last left) = τ 0
          · by_cases h2 : τ (Fin.last sep) = ρ 0
            · rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨h1.symm, rfl⟩,
                if_pos ⟨h2.symm, rfl⟩, if_pos ⟨h1, h2⟩]
            · have hright :
                  ¬ (ρ 0 = τ (Fin.last sep) ∧
                      ρ (Fin.last right) = ρ (Fin.last right)) := by
                intro he
                exact h2 he.1.symm
              have hrhs :
                  ¬ (σ (Fin.last left) = τ 0 ∧ τ (Fin.last sep) = ρ 0) := by
                intro h
                exact h2 h.2
              rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨h1.symm, rfl⟩, if_neg hright,
                if_neg hrhs]
              ring
          · have hmid :
                ¬ (τ 0 = σ (Fin.last left) ∧
                    τ (Fin.last sep) = τ (Fin.last sep)) := by
              intro he
              exact h1 he.1.symm
            have hrhs :
                ¬ (σ (Fin.last left) = τ 0 ∧ τ (Fin.last sep) = ρ 0) := by
              intro h
              exact h1 h.1
            rw [if_pos ⟨rfl, rfl⟩, if_neg hmid]
            simp [hrhs]
        · intro b _ hb
          simp [hb.symm]
        · intro hni
          exact absurd (Finset.mem_univ _) hni
      · intro y _ hy
        refine Finset.sum_eq_zero (fun b _ => ?_)
        simp [hy.symm]
      · intro hni
        exact absurd (Finset.mem_univ _) hni
    · intro x _ hx
      refine Finset.sum_eq_zero (fun y _ => Finset.sum_eq_zero (fun b _ => ?_))
      simp [hx.symm]
    · intro hni
      exact absurd (Finset.mem_univ _) hni
  · intro a _ ha
    refine Finset.sum_eq_zero (fun x _ =>
      Finset.sum_eq_zero (fun y _ => Finset.sum_eq_zero (fun b _ => ?_)))
    simp [ha.symm]
  · intro hni
    exact absurd (Finset.mem_univ _) hni

/-- The boundary-vector matrix product for the open two-marked numerator expands
to the four-endpoint matrix-power sum. -/
theorem layerOpenTwoMarkedMatrixProductNumerator_eq_matrixPower
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f g : Ω → ℝ)
    (left sep right : ℕ) :
    layerOpenTwoMarkedMatrixProductNumerator u k f g left sep right =
      layerOpenTwoMarkedMatrixPowerNumerator u k f g left sep right := by
  unfold layerOpenTwoMarkedMatrixProductNumerator
    layerOpenTwoMarkedMatrixPowerNumerator
  simp only
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  calc
    ∑ b, ∑ y, ∑ x,
        u a * ((layerTransferMatrix u k ^ left) a x * f x *
          (layerTransferMatrix u k ^ sep) x y * g y *
          (layerTransferMatrix u k ^ right) y b)
        = ∑ y, ∑ b, ∑ x,
            u a * ((layerTransferMatrix u k ^ left) a x * f x *
              (layerTransferMatrix u k ^ sep) x y * g y *
              (layerTransferMatrix u k ^ right) y b) := by
          rw [Finset.sum_comm]
    _ = ∑ y, ∑ x, ∑ b,
            u a * ((layerTransferMatrix u k ^ left) a x * f x *
              (layerTransferMatrix u k ^ sep) x y * g y *
              (layerTransferMatrix u k ^ right) y b) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.sum_comm]
    _ = ∑ x, ∑ y, ∑ b,
            u a * ((layerTransferMatrix u k ^ left) a x * f x *
              (layerTransferMatrix u k ^ sep) x y * g y *
              (layerTransferMatrix u k ^ right) y b) := by
          rw [Finset.sum_comm]
    _ = ∑ x, ∑ y, ∑ b,
            u a * f x * g y * (layerTransferMatrix u k ^ left) a x *
              (layerTransferMatrix u k ^ sep) x y *
              (layerTransferMatrix u k ^ right) y b := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          apply Finset.sum_congr rfl
          intro b _
          ring

/-- The four-endpoint matrix-power expression for the open two-marked numerator
is the single-open-path two-marked transfer numerator. -/
theorem layerOpenTwoMarkedMatrixPowerNumerator_eq_transferTwoPointNumerator
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f g : Ω → ℝ)
    (left sep right : ℕ) :
    layerOpenTwoMarkedMatrixPowerNumerator u k f g left sep right =
      layerOpenTwoMarkedTransferTwoPointNumerator u k f g left sep right := by
  unfold layerOpenTwoMarkedMatrixPowerNumerator
    layerOpenTwoMarkedTransferTwoPointNumerator
  rw [openTwoMarkedMatrixPowerSum_eq_pathTripleNumerator,
    openTwoMarkedPathTripleNumerator_eq_singlePathSum]

/-- The boundary-vector matrix-product expression for the open two-marked
numerator is the single-open-path two-marked transfer numerator. -/
theorem layerOpenTwoMarkedMatrixProductNumerator_eq_transferTwoPointNumerator
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f g : Ω → ℝ)
    (left sep right : ℕ) :
    layerOpenTwoMarkedMatrixProductNumerator u k f g left sep right =
      layerOpenTwoMarkedTransferTwoPointNumerator u k f g left sep right := by
  rw [layerOpenTwoMarkedMatrixProductNumerator_eq_matrixPower,
    layerOpenTwoMarkedMatrixPowerNumerator_eq_transferTwoPointNumerator]

/-- The open two-marked matrix-product numerator is the balanced boundary-vector
two-marked product after the diagonal similarity. -/
theorem layerOpenTwoMarkedMatrixProductNumerator_eq_balancedBoundaryTwoMarkedProduct
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f g : Ω → ℝ)
    (hu : ∀ a, 0 < u a) (left sep right : ℕ) :
    layerOpenTwoMarkedMatrixProductNumerator u k f g left sep right =
      RealOrthogonalSpectralData.boundaryTwoMarkedProduct
        (layerSymmetricTransferMatrix u k)
        (layerOpenBalancedBoundaryVector u) f g
        (layerOpenBalancedBoundaryVector u) left sep right := by
  let S := layerSymmetricTransferMatrix u k
  let D := layerTransferSqrtDiagonal u
  let Dinv := layerTransferSqrtDiagonalInv u
  let F := Matrix.diagonal f
  let Gm := Matrix.diagonal g
  have hT : layerTransferMatrix u k = Dinv * S * D :=
    layerTransferMatrix_eq_sqrtDiagonalInv_mul_symm_mul_sqrtDiagonal u k hu
  have hDinvD : Dinv * D = 1 := layerTransferSqrtDiagonalInv_mul_sqrtDiagonal u hu
  have hDDinv : D * Dinv = 1 := layerTransferSqrtDiagonal_mul_sqrtDiagonalInv u hu
  have hFD : F * D = D * F := by
    dsimp [F, D, layerTransferSqrtDiagonal]
    exact diagonal_mul_comm f fun x => Real.sqrt (u x)
  have hGD : Gm * D = D * Gm := by
    dsimp [Gm, D, layerTransferSqrtDiagonal]
    exact diagonal_mul_comm g fun x => Real.sqrt (u x)
  have hprod :
      layerTransferMatrix u k ^ left * F * layerTransferMatrix u k ^ sep *
          Gm * layerTransferMatrix u k ^ right =
        Dinv * (S ^ left * F * S ^ sep * Gm * S ^ right) * D := by
    rw [hT, matrix_conj_pow S Dinv D hDinvD hDDinv left,
      matrix_conj_pow S Dinv D hDinvD hDDinv sep,
      matrix_conj_pow S Dinv D hDinvD hDDinv right]
    calc
      (Dinv * S ^ left * D) * F * (Dinv * S ^ sep * D) * Gm *
          (Dinv * S ^ right * D)
          = Dinv * S ^ left * (D * F) * Dinv * S ^ sep * (D * Gm) *
              Dinv * S ^ right * D := by
            noncomm_ring
      _ = Dinv * S ^ left * (F * D) * Dinv * S ^ sep * (Gm * D) *
              Dinv * S ^ right * D := by
            rw [hFD, hGD]
      _ = Dinv * (S ^ left * F * S ^ sep * Gm * S ^ right) * D := by
            noncomm_ring [hDDinv]
  unfold layerOpenTwoMarkedMatrixProductNumerator
    RealOrthogonalSpectralData.boundaryTwoMarkedProduct layerOpenBalancedBoundaryVector
  dsimp only
  rw [hprod]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp [Dinv, D, layerTransferSqrtDiagonalInv, layerTransferSqrtDiagonal,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  field_simp [(Real.sqrt_pos_of_pos (hu a)).ne']
  rw [Real.sq_sqrt (le_of_lt (hu a))]
  ring

/-- The open two-marked matrix-product numerator in boundary-vector spectral
coordinates for the balanced transfer matrix. -/
theorem layerOpenTwoMarkedMatrixProductNumerator_eq_boundarySpectralSum
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f g : Ω → ℝ)
    (hu : ∀ a, 0 < u a)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (left sep right : ℕ) :
    layerOpenTwoMarkedMatrixProductNumerator u k f g left sep right =
      ∑ i, ∑ j, ∑ l,
        E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) i *
        E.eigenvalue i ^ left *
        E.markedMatrix f i j *
        E.eigenvalue j ^ sep *
        E.markedMatrix g j l *
        E.eigenvalue l ^ right *
        E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) l := by
  rw [layerOpenTwoMarkedMatrixProductNumerator_eq_balancedBoundaryTwoMarkedProduct
    u k f g hu left sep right]
  exact RealOrthogonalSpectralData.boundaryTwoMarkedProduct_eq_spectralSum
    E (layerOpenBalancedBoundaryVector u) f g (layerOpenBalancedBoundaryVector u)
    left sep right

/-- A boundary-vector spectral estimate bounds the open two-marked
matrix-product numerator in the marked separation. -/
theorem layerOpenTwoMarkedMatrixProductNumerator_abs_le_boundaryTwoMarkedSpectralPrefactor
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f g : Ω → ℝ)
    (hu : ∀ a, 0 < u a)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (eigenvalue_abs_le_scale : ∀ i, |E.eigenvalue i| ≤ scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (central_dominant_channel_zero : ∀ i l,
      E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) i *
        E.markedMatrix f i top *
        E.markedMatrix g top l *
        E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) l = 0)
    (left sep right : ℕ) :
    |layerOpenTwoMarkedMatrixProductNumerator u k f g left sep right|
      ≤ E.boundaryTwoMarkedSpectralPrefactor f g
          (layerOpenBalancedBoundaryVector u) (layerOpenBalancedBoundaryVector u) *
        scale ^ (left + sep + right) * theta ^ sep := by
  rw [layerOpenTwoMarkedMatrixProductNumerator_eq_boundarySpectralSum u k f g hu E
    left sep right]
  exact RealOrthogonalSpectralData.boundaryTwoMarkedSpectralSum_abs_le_spectralPrefactor
    E f g (layerOpenBalancedBoundaryVector u) (layerOpenBalancedBoundaryVector u)
    top scale theta scale_pos theta_nonneg eigenvalue_abs_le_scale
    subdominant_abs_le central_dominant_channel_zero left sep right

/-! ## Two-marked open certificate -/

/-- A finite open-boundary two-marked min-gap certificate.  It is the two-mark
analogue of `LayerOpenMinSpectralGapCertificate`: the partition lower bound is
mark-agnostic, while the numerator estimate now carries two distinct marks `f`
(left cut) and `g` (right cut). -/
structure LayerOpenTwoMarkedMinSpectralGapCertificate
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f g : Ω → ℝ) where
  /-- The reference exponential scale. -/
  scale : ℝ
  /-- The decay rate. -/
  theta : ℝ
  /-- Numerator prefactor. -/
  prefactor : ℝ
  /-- Denominator prefactor. -/
  partitionPrefactor : ℝ
  /-- Positivity of the reference scale. -/
  scale_pos : 0 < scale
  /-- Nonnegativity of the decay rate. -/
  theta_nonneg : 0 ≤ theta
  /-- Strict contraction of the decay rate. -/
  theta_lt_one : theta < 1
  /-- Nonnegativity of the numerator prefactor. -/
  prefactor_nonneg : 0 ≤ prefactor
  /-- Positivity of the denominator prefactor. -/
  partitionPrefactor_pos : 0 < partitionPrefactor
  /-- Uniform lower bound on the open partition sum. -/
  partition_lower :
    ∀ {n : ℕ}, partitionPrefactor * scale ^ n ≤ layerOpenTransferPartition u k n
  /-- Uniform two-insertion numerator estimate with open boundary buffers. -/
  marked_abs_le :
    ∀ left sep right : ℕ,
      |layerOpenTwoMarkedTransferTwoPointNumerator u k f g left sep right| ≤
        prefactor * scale ^ (left + sep + right) * theta ^ sep

/-- The normalised open finite layer two-marked two-point function. -/
noncomputable def layerOpenTwoMarkedTwoPoint
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f g : Ω → ℝ)
    (left sep right : ℕ) : ℝ :=
  layerOpenTwoMarkedTransferTwoPointNumerator u k f g left sep right
    / layerOpenPartition u k (left + sep + right)

omit [DecidableEq Ω] in
/-- A finite open-boundary two-marked min-gap certificate gives the normalised
open two-marked two-point decay bound. -/
theorem layerOpenTwoMarkedTwoPoint_abs_le_of_cert
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} {f g : Ω → ℝ}
    (cert : LayerOpenTwoMarkedMinSpectralGapCertificate u k f g)
    (left sep right : ℕ) :
    |layerOpenTwoMarkedTwoPoint u k f g left sep right| ≤
      (cert.prefactor / cert.partitionPrefactor) * cert.theta ^ sep := by
  let n := left + sep + right
  have hscaleN : 0 < cert.scale ^ n := pow_pos cert.scale_pos n
  have hθ : 0 ≤ cert.theta ^ sep := pow_nonneg cert.theta_nonneg sep
  have hlower_pos : 0 < cert.partitionPrefactor * cert.scale ^ n :=
    mul_pos cert.partitionPrefactor_pos hscaleN
  have hden_lower : cert.partitionPrefactor * cert.scale ^ n
      ≤ layerOpenPartition u k n := by
    rw [layerOpenPartition_eq_transfer]
    exact cert.partition_lower
  have hden_pos : 0 < layerOpenPartition u k n :=
    lt_of_lt_of_le hlower_pos hden_lower
  have hmarked :
      |layerOpenTwoMarkedTransferTwoPointNumerator u k f g left sep right|
        ≤ cert.prefactor * cert.scale ^ n * cert.theta ^ sep :=
    cert.marked_abs_le left sep right
  rw [layerOpenTwoMarkedTwoPoint, abs_div, abs_of_pos hden_pos]
  calc
    |layerOpenTwoMarkedTransferTwoPointNumerator u k f g left sep right|
        / layerOpenPartition u k n
        = |layerOpenTwoMarkedTransferTwoPointNumerator u k f g left sep right|
          * (layerOpenPartition u k n)⁻¹ := by
            rw [div_eq_mul_inv]
    _ ≤ (cert.prefactor * cert.scale ^ n * cert.theta ^ sep)
          * (cert.partitionPrefactor * cert.scale ^ n)⁻¹ := by
            exact mul_le_mul hmarked ((inv_le_inv₀ hden_pos hlower_pos).mpr hden_lower)
              (inv_nonneg.mpr hden_pos.le)
              (mul_nonneg (mul_nonneg cert.prefactor_nonneg hscaleN.le) hθ)
    _ = (cert.prefactor / cert.partitionPrefactor) * cert.theta ^ sep := by
            field_simp [(ne_of_gt cert.partitionPrefactor_pos), (ne_of_gt hscaleN)]

/-- Constructor for an open two-marked min-gap certificate from boundary-vector
orthogonal spectral numerator bounds and the matching spectral denominator
lower bound.  The denominator infrastructure is shared with the single-mark
route; only the two-marked numerator estimate is specific. -/
noncomputable def
    layerOpenTwoMarkedMinSpectralGapCertificate_of_orthogonalBoundaryDominantBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f g : Ω → ℝ)
    (hu : ∀ a, 0 < u a)
    (E : RealOrthogonalSpectralData (layerSymmetricTransferMatrix u k))
    (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_pos :
      0 < E.boundarySpectralPartitionPrefactor
        (layerOpenBalancedBoundaryVector u) top theta)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (central_dominant_channel_zero : ∀ i l,
      E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) i *
        E.markedMatrix f i top *
        E.markedMatrix g top l *
        E.boundaryCoordinates (layerOpenBalancedBoundaryVector u) l = 0) :
    LayerOpenTwoMarkedMinSpectralGapCertificate u k f g where
  scale := scale
  theta := theta
  prefactor :=
    E.boundaryTwoMarkedSpectralPrefactor f g
      (layerOpenBalancedBoundaryVector u) (layerOpenBalancedBoundaryVector u)
  partitionPrefactor :=
    E.boundarySpectralPartitionPrefactor (layerOpenBalancedBoundaryVector u) top theta
  scale_pos := scale_pos
  theta_nonneg := theta_nonneg
  theta_lt_one := theta_lt_one
  prefactor_nonneg :=
    E.boundaryTwoMarkedSpectralPrefactor_nonneg f g
      (layerOpenBalancedBoundaryVector u) (layerOpenBalancedBoundaryVector u)
  partitionPrefactor_pos := partitionPrefactor_pos
  partition_lower := fun {n} => by
    rw [layerOpenTransferPartition_eq_matrixPartition]
    exact layerOpenMatrixPartition_lower_of_orthogonalBoundaryDominantBounds
      u k hu E top scale theta scale_pos theta_nonneg (le_of_lt theta_lt_one)
      dominant_eigenvalue subdominant_abs_le n
  marked_abs_le := fun left sep right => by
    rw [← layerOpenTwoMarkedMatrixProductNumerator_eq_transferTwoPointNumerator
      u k f g left sep right]
    exact layerOpenTwoMarkedMatrixProductNumerator_abs_le_boundaryTwoMarkedSpectralPrefactor
      u k f g hu E top scale theta scale_pos theta_nonneg
      (E.eigenvalue_abs_le_scale_of_dominant_bounds top scale theta scale_pos
        (le_of_lt theta_lt_one) dominant_eigenvalue subdominant_abs_le)
      subdominant_abs_le central_dominant_channel_zero left sep right

/-! ## Cross-transverse-site correlation equate lemma -/

/-- The normalised cross-transverse-site two-point function on the concrete open
layer slab.  The first mark is `layerSpinAt x` (left endpoint) and the second is
`layerSpinAt y` (right endpoint). -/
noncomputable def layerOpenSlabSpinTwoMarkedTwoPoint {S : Type*}
    [Fintype S] [DecidableEq S]
    (u : LayerState S → ℝ) (k : LayerState S → LayerState S → ℝ)
    (x y : S) (left sep right : ℕ) : ℝ :=
  layerOpenTwoMarkedTwoPoint u k (layerSpinAt x) (layerSpinAt y) left sep right

/-- The project-level cross-transverse-site two-point correlation on the finite
open-slab graph is the concrete open layer two-marked two-point function.  The
two sites `(left, x)` and `(left+sep, y)` are distinct because their layer
coordinates differ when `0 < sep`, so the genuine two-element observable expands
to the product of the two spin signs. -/
theorem correlation_layerOpenSlabGraph_two_transverse_eq_layerOpenSlabSpinTwoMarkedTwoPoint
    {S : Type*} [DecidableEq S] [Fintype S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (E : Finset (S × S))
    (p : IsingParams ℝ) (x y : S) (left sep right : ℕ) (hsep : 0 < sep) :
    correlation (layerOpenSlabGraph (S := S) H E (left + sep + right)) p
        ({Prod.mk (layerOpenLeftIndex left sep right) x,
          Prod.mk (layerOpenRightIndex left sep right) y} :
            Finset (LayerOpenSlabSite (left + sep + right) S)) =
      layerOpenSlabSpinTwoMarkedTwoPoint
        (layerInternalWeight H p) (layerTransitionWeight E p) x y
        left sep right := by
  let n := left + sep + right
  have hsite :
      (Prod.mk (layerOpenLeftIndex left sep right) x :
          LayerOpenSlabSite n S) ≠
        Prod.mk (layerOpenRightIndex left sep right) y := by
    intro h
    have hv := congr_arg (fun ix : LayerOpenSlabSite n S => ix.1.val) h
    simp [layerOpenLeftIndex, layerOpenRightIndex] at hv
    omega
  unfold correlation gibbsExpectation
  rw [partitionFunction_layerOpenSlabGraph_eq_isingLayerOpenSlabPartition
    (S := S) H E p]
  unfold isingLayerOpenSlabPartition
  have hsum :
      (∑ σ : Config (LayerOpenSlabSite n S),
          spinProduct
              ({Prod.mk (layerOpenLeftIndex left sep right) x,
                Prod.mk (layerOpenRightIndex left sep right) y} :
                Finset (LayerOpenSlabSite n S)) σ *
            boltzmannWeight (layerOpenSlabGraph (S := S) H E n) p σ)
        =
        ∑ σ : Config (LayerOpenSlabSite n S),
          Spin.sign ℝ (σ (layerOpenLeftIndex left sep right, x))
            * Spin.sign ℝ (σ (layerOpenRightIndex left sep right, y))
            * layerOpenStackWeight
              (layerInternalWeight H p) (layerTransitionWeight E p)
              ((layerOpenSlabConfigEquiv (S := S) n) σ) := by
    refine Finset.sum_congr rfl ?_
    intro σ _
    rw [boltzmannWeight_layerOpenSlabGraph_eq_layerOpenStackWeight
      (S := S) H E p σ]
    simp [spinProduct, Spin.sign, hsite, mul_assoc]
  rw [hsum]
  unfold layerOpenSlabSpinTwoMarkedTwoPoint layerOpenTwoMarkedTwoPoint
    layerOpenTwoMarkedTransferTwoPointNumerator layerSpinAt
  rw [div_eq_mul_inv,
    mul_comm (∑ c : Fin (n + 1) → LayerState S,
      Spin.sign ℝ (c (layerOpenLeftIndex left sep right) x) *
        Spin.sign ℝ (c (layerOpenRightIndex left sep right) y) *
        (layerInternalWeight H p (c 0) *
          pathWeight (layerTransferMatrix (layerInternalWeight H p)
            (layerTransitionWeight E p)) c))]
  congr 1
  refine Fintype.sum_equiv (layerOpenSlabConfigEquiv (S := S) n)
    (fun σ : Config (LayerOpenSlabSite n S) =>
      Spin.sign ℝ (σ (layerOpenLeftIndex left sep right, x)) *
        Spin.sign ℝ (σ (layerOpenRightIndex left sep right, y)) *
        layerOpenStackWeight (layerInternalWeight H p) (layerTransitionWeight E p)
          ((layerOpenSlabConfigEquiv (S := S) n) σ))
    (fun c : Fin (n + 1) → LayerState S =>
      Spin.sign ℝ (c (layerOpenLeftIndex left sep right) x) *
        Spin.sign ℝ (c (layerOpenRightIndex left sep right) y) *
        (layerInternalWeight H p (c 0) *
          pathWeight (layerTransferMatrix (layerInternalWeight H p)
            (layerTransitionWeight E p)) c))
    (fun _ => rfl)

/-! ## Cross-transverse-site general-layer decay theorem -/

/-- Orthogonal boundary-dominance hypotheses give project-level finite open-slab
*cross*-transverse-site correlation decay, with the denominator lower bound
discharged by the spectral denominator bridge.  This is the two-mark analogue of
`correlation_layerOpenSlabGraph_same_transverse_abs_le_of_boundarySpectralDenominator`;
the same-site case is the `x = y` specialisation. -/
theorem
    correlation_layerOpenSlabGraph_two_transverse_abs_le_of_boundarySpectralDenominator
    {S : Type*} [Fintype S] [DecidableEq S]
    (H : SimpleGraph S) [Fintype H.edgeSet] (transitionPairs : Finset (S × S))
    (p : IsingParams ℝ) (x y : S)
    (spec : RealOrthogonalSpectralData
      (layerSymmetricTransferMatrix
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)))
    (top : LayerState S) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (partitionPrefactor_pos :
      0 < spec.boundarySpectralPartitionPrefactor
        (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) top theta)
    (dominant_eigenvalue : spec.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |spec.eigenvalue i| ≤ theta * scale)
    (central_dominant_channel_zero : ∀ i l,
      spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) i *
        spec.markedMatrix (layerSpinAt x) i top *
        spec.markedMatrix (layerSpinAt y) top l *
        spec.boundaryCoordinates
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) l = 0)
    (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (layerOpenSlabGraph (S := S) H transitionPairs (left + sep + right)) p
      ({Prod.mk (layerOpenLeftIndex left sep right) x,
        Prod.mk (layerOpenRightIndex left sep right) y} :
          Finset (LayerOpenSlabSite (left + sep + right) S))|
      ≤
        (spec.boundaryTwoMarkedSpectralPrefactor (layerSpinAt x) (layerSpinAt y)
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p))
          (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) /
            spec.boundarySpectralPartitionPrefactor
              (layerOpenBalancedBoundaryVector (layerInternalWeight H p)) top theta) *
          theta ^ sep := by
  let cert :
      LayerOpenTwoMarkedMinSpectralGapCertificate
        (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
        (layerSpinAt x) (layerSpinAt y) :=
    layerOpenTwoMarkedMinSpectralGapCertificate_of_orthogonalBoundaryDominantBounds
      (layerInternalWeight H p) (layerTransitionWeight transitionPairs p)
      (layerSpinAt x) (layerSpinAt y) (fun _ => Real.exp_pos _) spec top scale theta
      scale_pos theta_nonneg theta_lt_one partitionPrefactor_pos
      dominant_eigenvalue subdominant_abs_le central_dominant_channel_zero
  rw [correlation_layerOpenSlabGraph_two_transverse_eq_layerOpenSlabSpinTwoMarkedTwoPoint
    (S := S) H transitionPairs p x y left sep right hsep]
  exact layerOpenTwoMarkedTwoPoint_abs_le_of_cert cert left sep right

end TransferMatrix

end IsingModel
