import IsingModel.TransferMatrix.LayerOpenTwoMarkedSpectralDecay.Spectral
import IsingModel.TransferMatrix.LayerOpenSlabGraph
import IsingModel.TransferMatrix.LayerOpenSpectral
import IsingModel.TransferMatrix.LayerOpenSpectralDenominator

/-!
# Finite open layer-slab two-marked spectral decay: open numerator chain

This is the numerator child of
`IsingModel.TransferMatrix.LayerOpenTwoMarkedSpectralDecay`.  It develops the
open two-marked numerator from its boundary-vector matrix product through the
three-open-path expansion to the single-open-path transfer numerator, and then
in balanced boundary-vector spectral coordinates, culminating in the numerator
spectral-prefactor absolute bound.

See the umbrella module `LayerOpenTwoMarkedSpectralDecay` for the overview and
references.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

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

end TransferMatrix

end IsingModel
