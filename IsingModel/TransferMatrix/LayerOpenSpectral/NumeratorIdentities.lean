import IsingModel.TransferMatrix.LayerOpenSpectral.PathGlue

/-!
# Open-boundary marked numerator identities

Finite-sum identities equating the boundary-vector marked matrix-power/product
numerators with the existing open transfer two-point numerator.

This is a build-speed split child of `LayerOpenSpectral`; see that umbrella
module for the mathematical overview and references.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Reorder seven nested `Finset.univ` sums, moving the last three indices to the
front. -/
private theorem sum_reorder_7 {A B C D E F G R : Type*} [Fintype A] [Fintype B]
    [Fintype C] [Fintype D] [Fintype E] [Fintype F] [Fintype G] [AddCommMonoid R]
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

/-- The three-path open marked numerator is the same finite sum as the single
open-path transfer numerator with two marked positions. -/
theorem openMarkedPathTripleNumerator_eq_singlePathSum
    (M : Matrix Ω Ω ℝ) (w d : Ω → ℝ)
    (left sep right : ℕ) :
    openMarkedPathTripleNumerator M w d left sep right =
      ∑ c : Fin (left + sep + right + 1) → Ω,
        d (c (layerOpenLeftIndex left sep right))
          * d (c (layerOpenRightIndex left sep right))
          * (w (c 0) * pathWeight M c) := by
  unfold openMarkedPathTripleNumerator
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

/-- The four-endpoint matrix-power sum expands to the three glued open-path
sum. -/
theorem openMarkedMatrixPowerSum_eq_pathTripleNumerator
    (M : Matrix Ω Ω ℝ) (w d : Ω → ℝ)
    (left sep right : ℕ) :
    (∑ a : Ω, ∑ x : Ω, ∑ y : Ω, ∑ b : Ω,
      w a * d x * d y * (M ^ left) a x * (M ^ sep) x y * (M ^ right) y b) =
      openMarkedPathTripleNumerator M w d left sep right := by
  unfold openMarkedPathTripleNumerator
  simp_rw [pow_apply_eq_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [sum_reorder_7 (A := Ω) (B := Ω) (C := Ω) (D := Ω)
    (E := Fin (right + 1) → Ω) (F := Fin (sep + 1) → Ω) (G := Fin (left + 1) → Ω)
    (H := fun a x y b ρ τ σ =>
      ((w a * d x * d y *
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

/-- The boundary-vector matrix product for the open marked numerator expands to
the four-endpoint matrix-power sum.  This is only the finite matrix algebra
step; it does not identify the expression with the existing open path
numerator or with a spectral-basis expansion. -/
theorem layerOpenTwoPointMatrixProductNumerator_eq_matrixPower
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (left sep right : ℕ) :
    layerOpenTwoPointMatrixProductNumerator u k f left sep right =
      layerOpenTwoPointMatrixPowerNumerator u k f left sep right := by
  unfold layerOpenTwoPointMatrixProductNumerator layerOpenTwoPointMatrixPowerNumerator
  simp only
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  calc
    ∑ b, ∑ y, ∑ x,
        u a * ((layerTransferMatrix u k ^ left) a x * f x *
          (layerTransferMatrix u k ^ sep) x y * f y *
          (layerTransferMatrix u k ^ right) y b)
        = ∑ y, ∑ b, ∑ x,
            u a * ((layerTransferMatrix u k ^ left) a x * f x *
              (layerTransferMatrix u k ^ sep) x y * f y *
              (layerTransferMatrix u k ^ right) y b) := by
          rw [Finset.sum_comm]
    _ = ∑ y, ∑ x, ∑ b,
            u a * ((layerTransferMatrix u k ^ left) a x * f x *
              (layerTransferMatrix u k ^ sep) x y * f y *
              (layerTransferMatrix u k ^ right) y b) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.sum_comm]
    _ = ∑ x, ∑ y, ∑ b,
            u a * ((layerTransferMatrix u k ^ left) a x * f x *
              (layerTransferMatrix u k ^ sep) x y * f y *
              (layerTransferMatrix u k ^ right) y b) := by
          rw [Finset.sum_comm]
    _ = ∑ x, ∑ y, ∑ b,
            u a * f x * f y * (layerTransferMatrix u k ^ left) a x *
              (layerTransferMatrix u k ^ sep) x y *
              (layerTransferMatrix u k ^ right) y b := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          apply Finset.sum_congr rfl
          intro b _
          ring

/-- The four-endpoint matrix-power expression for the open marked numerator is
the existing single-open-path transfer numerator. -/
theorem layerOpenTwoPointMatrixPowerNumerator_eq_transferTwoPointNumerator
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (left sep right : ℕ) :
    layerOpenTwoPointMatrixPowerNumerator u k f left sep right =
      layerOpenTransferTwoPointNumerator u k f left sep right := by
  unfold layerOpenTwoPointMatrixPowerNumerator layerOpenTransferTwoPointNumerator
  rw [openMarkedMatrixPowerSum_eq_pathTripleNumerator,
    openMarkedPathTripleNumerator_eq_singlePathSum]

/-- The boundary-vector matrix-product expression for the open marked numerator
is the existing single-open-path transfer numerator. -/
theorem layerOpenTwoPointMatrixProductNumerator_eq_transferTwoPointNumerator
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (left sep right : ℕ) :
    layerOpenTwoPointMatrixProductNumerator u k f left sep right =
      layerOpenTransferTwoPointNumerator u k f left sep right := by
  rw [layerOpenTwoPointMatrixProductNumerator_eq_matrixPower,
    layerOpenTwoPointMatrixPowerNumerator_eq_transferTwoPointNumerator]

end TransferMatrix

end IsingModel
