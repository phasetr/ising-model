import IsingModel.TransferMatrix.LayerOpenSlab

/-!
# Open-boundary layer spectral bridges

This file is the finite open-boundary counterpart of the cyclic spectral
certificate constructors.  It rewrites the open layer partition as a
boundary-vector matrix-power sum and packages explicit open-path bounds into
the existing open min-gap certificate.

The results are finite and conditional.  They do not prove a physical
interacting spectral window, a Perron--Frobenius theorem, a thermodynamic limit,
or final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Boundary-vector matrix-power form -/

/-- The finite open partition written as the boundary-vector matrix-power sum
`∑ a b, u a * (T^n) a b`, where `T = layerTransferMatrix u k`. -/
def layerOpenMatrixPartition (u : Ω → ℝ) (k : Ω → Ω → ℝ) (n : ℕ) : ℝ :=
  ∑ a : Ω, ∑ b : Ω, u a * (layerTransferMatrix u k ^ n) a b

/-- The open transfer partition is the boundary-vector matrix-power sum. -/
theorem layerOpenTransferPartition_eq_matrixPartition
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (n : ℕ) :
    layerOpenTransferPartition u k n = layerOpenMatrixPartition u k n := by
  unfold layerOpenTransferPartition layerOpenMatrixPartition
  calc
    ∑ c : Fin (n + 1) → Ω,
        u (c 0) * pathWeight (layerTransferMatrix u k) c
        =
        ∑ c : Fin (n + 1) → Ω, ∑ a : Ω, ∑ b : Ω,
          u a *
            (if c 0 = a ∧ c (Fin.last n) = b then
              pathWeight (layerTransferMatrix u k) c
            else 0) := by
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_eq_single (c 0)]
          · rw [Finset.sum_eq_single (c (Fin.last n))]
            · simp
            · intro b _ hb
              simp [hb.symm]
            · intro h
              exact absurd (Finset.mem_univ (c (Fin.last n))) h
          · intro a _ ha
            simp [ha.symm]
          · intro h
            exact absurd (Finset.mem_univ (c 0)) h
    _ =
        ∑ a : Ω, ∑ b : Ω, ∑ c : Fin (n + 1) → Ω,
          u a *
            (if c 0 = a ∧ c (Fin.last n) = b then
              pathWeight (layerTransferMatrix u k) c
            else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ =
        ∑ a : Ω, ∑ b : Ω,
          u a * ∑ c : Fin (n + 1) → Ω,
            (if c 0 = a ∧ c (Fin.last n) = b then
              pathWeight (layerTransferMatrix u k) c
            else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.mul_sum]
    _ =
        ∑ a : Ω, ∑ b : Ω, u a * (layerTransferMatrix u k ^ n) a b := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [pow_apply_eq_sum]

/-- The open Gibbs partition is the boundary-vector matrix-power sum. -/
theorem layerOpenPartition_eq_matrixPartition
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (n : ℕ) :
    layerOpenPartition u k n = layerOpenMatrixPartition u k n := by
  rw [layerOpenPartition_eq_transfer, layerOpenTransferPartition_eq_matrixPartition]

/-! ## Marked numerator matrix-power form -/

/-- Reorder seven nested `Finset.univ` sums, moving the last three indices to the
front. -/
theorem sum_reorder_7 {A B C D E F G R : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Fintype D] [Fintype E] [Fintype F] [Fintype G] [AddCommMonoid R]
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

/-- The finite open marked numerator as the boundary-vector matrix product
`u^T T^left D_f T^sep D_f T^right 1`, before expanding the matrix products into
endpoint sums. -/
noncomputable def layerOpenTwoPointMatrixProductNumerator
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (left sep right : ℕ) : ℝ :=
  let M := layerTransferMatrix u k
  ∑ a : Ω, ∑ b : Ω,
    u a * (M ^ left * Matrix.diagonal f * M ^ sep * Matrix.diagonal f * M ^ right) a b

/-- The finite open marked numerator matrix-power expression expanded as a
four-endpoint sum.  This is the finite-sum form of
`u^T T^left D_f T^sep D_f T^right 1`, with
`T = layerTransferMatrix u k`. -/
noncomputable def layerOpenTwoPointMatrixPowerNumerator
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (left sep right : ℕ) : ℝ :=
  let M := layerTransferMatrix u k
  ∑ a : Ω, ∑ x : Ω, ∑ y : Ω, ∑ b : Ω,
    u a * f x * f y * (M ^ left) a x * (M ^ sep) x y * (M ^ right) y b

/-- The three-open-path expansion of an open marked matrix-power numerator. -/
noncomputable def openMarkedPathTripleNumerator
    (M : Matrix Ω Ω ℝ) (w d : Ω → ℝ)
    (left sep right : ℕ) : ℝ :=
  ∑ σ : Fin (left + 1) → Ω,
  ∑ τ : Fin (sep + 1) → Ω,
  ∑ ρ : Fin (right + 1) → Ω,
    if σ (Fin.last left) = τ 0 ∧ τ (Fin.last sep) = ρ 0 then
      w (σ 0) * d (σ (Fin.last left)) * d (τ (Fin.last sep)) *
        pathWeight M σ * pathWeight M τ * pathWeight M ρ
    else 0

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

/-! ## Certificate constructors -/

/-- Constructor for an open min-gap certificate from explicit open transfer
bounds.  This is the open-boundary analogue of the cyclic trace-bound
constructors: it packages already-proved finite open denominator and numerator
estimates into the certificate consumed by open slab correlation bounds. -/
def layerOpenMinSpectralGapCertificate_of_transferBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower : ∀ {n : ℕ},
      partitionPrefactor * scale ^ n ≤ layerOpenTransferPartition u k n)
    (marked_abs_le : ∀ left sep right : ℕ,
      |layerOpenTransferTwoPointNumerator u k f left sep right| ≤
        prefactor * scale ^ (left + sep + right) * theta ^ sep) :
    LayerOpenMinSpectralGapCertificate u k f where
  scale := scale
  theta := theta
  prefactor := prefactor
  partitionPrefactor := partitionPrefactor
  scale_pos := scale_pos
  theta_nonneg := theta_nonneg
  theta_lt_one := theta_lt_one
  prefactor_nonneg := prefactor_nonneg
  partitionPrefactor_pos := partitionPrefactor_pos
  partition_lower := partition_lower
  marked_abs_le := marked_abs_le

/-- Constructor for an open min-gap certificate whose denominator estimate is
proved in boundary-vector matrix-power form.  The marked numerator remains the
open-path numerator used by `LayerOpenMinSpectralGapCertificate`; later spectral
files can refine that input by proving a matrix-power or spectral-basis formula
for the marked open path. -/
def layerOpenMinSpectralGapCertificate_of_matrixPartitionBounds
    (u : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℝ)
    (scale theta prefactor partitionPrefactor : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_lt_one : theta < 1)
    (prefactor_nonneg : 0 ≤ prefactor)
    (partitionPrefactor_pos : 0 < partitionPrefactor)
    (partition_lower_matrix : ∀ {n : ℕ},
      partitionPrefactor * scale ^ n ≤ layerOpenMatrixPartition u k n)
    (marked_abs_le : ∀ left sep right : ℕ,
      |layerOpenTransferTwoPointNumerator u k f left sep right| ≤
        prefactor * scale ^ (left + sep + right) * theta ^ sep) :
    LayerOpenMinSpectralGapCertificate u k f := by
  refine
    layerOpenMinSpectralGapCertificate_of_transferBounds u k f scale theta
      prefactor partitionPrefactor scale_pos theta_nonneg theta_lt_one
      prefactor_nonneg partitionPrefactor_pos ?_ marked_abs_le
  intro n
  rw [layerOpenTransferPartition_eq_matrixPartition]
  exact partition_lower_matrix

end TransferMatrix

end IsingModel
