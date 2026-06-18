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

omit [Fintype Ω] [DecidableEq Ω] in
/-- Glue two open paths into one open path, keeping their shared endpoint once.
This tail-based version has convenient endpoint behaviour; its path-weight
factorization is proved from `pathWeight_append`. -/
def openPathGlue {a b : ℕ} (σ : Fin (a + 1) → Ω) (τ : Fin (b + 1) → Ω) :
    Fin (a + b + 1) → Ω :=
  fun i => Fin.append σ (Fin.tail τ) (Fin.cast (by omega) i)

omit [Fintype Ω] [DecidableEq Ω] in
/-- The left component obtained by splitting a glued open path. -/
def openPathGlueLeft {a b : ℕ} (c : Fin (a + b + 1) → Ω) : Fin (a + 1) → Ω :=
  fun i => c (Fin.cast (by omega) (Fin.castAdd b i))

omit [Fintype Ω] [DecidableEq Ω] in
/-- The right component obtained by splitting a glued open path. -/
def openPathGlueRight {a b : ℕ} (c : Fin (a + b + 1) → Ω) : Fin (b + 1) → Ω :=
  Fin.cases (c ⟨a, by omega⟩)
    (fun i : Fin b => c (Fin.cast (by omega) (Fin.natAdd (a + 1) i)))

omit [Fintype Ω] [DecidableEq Ω] in
/-- A two-path glue starts at the first path. -/
theorem openPathGlue_apply_zero {a b : ℕ}
    (σ : Fin (a + 1) → Ω) (τ : Fin (b + 1) → Ω) :
    openPathGlue σ τ 0 = σ 0 := by
  unfold openPathGlue
  have hidx :
      Fin.cast (by omega) (0 : Fin (a + b + 1)) =
        Fin.castAdd b (0 : Fin (a + 1)) := by
    ext
    simp
  rw [hidx, Fin.append_left]

omit [Fintype Ω] [DecidableEq Ω] in
/-- At the end of the first path, a two-path glue has the first path's endpoint. -/
theorem openPathGlue_apply_first_last {a b : ℕ}
    (σ : Fin (a + 1) → Ω) (τ : Fin (b + 1) → Ω) :
    openPathGlue σ τ ⟨a, by omega⟩ = σ (Fin.last a) := by
  unfold openPathGlue
  have hidx :
      Fin.cast (by omega) (⟨a, by omega⟩ : Fin (a + b + 1)) =
        Fin.castAdd b (Fin.last a) := by
    ext
    simp
  rw [hidx, Fin.append_left]

omit [Fintype Ω] [DecidableEq Ω] in
/-- A point in the left component of a two-path glue evaluates in the first
path. -/
theorem openPathGlue_apply_left {a b : ℕ}
    (σ : Fin (a + 1) → Ω) (τ : Fin (b + 1) → Ω) (i : Fin (a + 1)) :
    openPathGlue σ τ (Fin.cast (by omega) (Fin.castAdd b i)) = σ i := by
  unfold openPathGlue
  have hidx :
      Fin.cast (by omega) (Fin.cast (by omega) (Fin.castAdd b i) :
          Fin (a + b + 1)) =
        Fin.castAdd b i := by
    ext
    simp
  rw [hidx, Fin.append_left]

omit [Fintype Ω] [DecidableEq Ω] in
/-- A point in the right component of a two-path glue evaluates in the tail of
the second path. -/
theorem openPathGlue_apply_right_succ {a b : ℕ}
    (σ : Fin (a + 1) → Ω) (τ : Fin (b + 1) → Ω) (i : Fin b) :
    openPathGlue σ τ (Fin.cast (by omega) (Fin.natAdd (a + 1) i)) = τ i.succ := by
  unfold openPathGlue
  have hidx :
      Fin.cast (by omega) (Fin.cast (by omega) (Fin.natAdd (a + 1) i) :
          Fin (a + b + 1)) =
        Fin.natAdd (a + 1) i := by
    ext
    simp
  rw [hidx, Fin.append_right, Fin.tail_def]

omit [Fintype Ω] [DecidableEq Ω] in
/-- Splitting a glued two-path open path recovers the left path. -/
theorem openPathGlueLeft_glue {a b : ℕ}
    (σ : Fin (a + 1) → Ω) (τ : Fin (b + 1) → Ω) :
    openPathGlueLeft (openPathGlue σ τ) = σ := by
  funext i
  unfold openPathGlueLeft
  rw [openPathGlue_apply_left]

omit [Fintype Ω] [DecidableEq Ω] in
/-- Splitting a glued two-path open path recovers the right path when the join
is valid. -/
theorem openPathGlueRight_glue {a b : ℕ}
    (σ : Fin (a + 1) → Ω) (τ : Fin (b + 1) → Ω)
    (hστ : σ (Fin.last a) = τ 0) :
    openPathGlueRight (openPathGlue σ τ) = τ := by
  funext i
  refine Fin.cases ?_ ?_ i
  · unfold openPathGlueRight
    simp only [Fin.cases_zero]
    rw [openPathGlue_apply_first_last, hστ]
  · intro j
    unfold openPathGlueRight
    simp only [Fin.cases_succ]
    rw [openPathGlue_apply_right_succ]

omit [Fintype Ω] [DecidableEq Ω] in
/-- Gluing the two split components of an open path recovers the original path. -/
theorem openPathGlue_split {a b : ℕ} (c : Fin (a + b + 1) → Ω) :
    openPathGlue (openPathGlueLeft c) (openPathGlueRight c) = c := by
  funext i
  unfold openPathGlue
  let j : Fin ((a + 1) + b) := Fin.cast (by omega) i
  change Fin.append (openPathGlueLeft c) (Fin.tail (openPathGlueRight c)) j = c i
  refine Fin.addCases (motive := fun j =>
    Fin.append (openPathGlueLeft c) (Fin.tail (openPathGlueRight c)) j =
      c (Fin.cast (by omega) j)) ?_ ?_ j
  · intro iL
    rw [Fin.append_left]
    unfold openPathGlueLeft
    congr 1
  · intro iR
    rw [Fin.append_right]
    unfold openPathGlueRight Fin.tail
    simp only [Fin.cases_succ]

omit [Fintype Ω] [DecidableEq Ω] in
/-- The tail-based two-path glue is the same path as the `init`-plus-whole-path
glue used by `pathWeight_append`, provided the endpoints agree. -/
theorem openPathGlue_eq_append_init {a b : ℕ}
    (σ : Fin (a + 1) → Ω) (τ : Fin (b + 1) → Ω)
    (hστ : σ (Fin.last a) = τ 0) :
    openPathGlue σ τ =
      fun i : Fin (a + b + 1) =>
        (Fin.append (Fin.init σ) τ) (Fin.cast (by omega) i) := by
  funext i
  unfold openPathGlue
  have hsource : ∀ j : Fin ((a + 1) + b),
      Fin.append σ (Fin.tail τ) j =
        (Fin.append (Fin.init σ) τ) (Fin.cast (by omega) j) := by
    intro j
    refine Fin.addCases (fun jL => ?_) (fun jR => ?_) j
    · rw [Fin.append_left]
      by_cases hj : (jL : ℕ) = a
      · have hlast : jL = Fin.last a := by
          ext
          exact hj
        subst hlast
        have hcast :
            Fin.cast (by omega) (Fin.castAdd b (Fin.last a : Fin (a + 1))) =
              Fin.natAdd a (0 : Fin (b + 1)) := by
          ext
          simp
        rw [hcast, Fin.append_right, hστ]
      · have hlt : (jL : ℕ) < a := by
          have hle : (jL : ℕ) ≤ a := Nat.le_of_lt_succ jL.isLt
          exact Nat.lt_of_le_of_ne hle hj
        have hcast :
            Fin.cast (by omega) (Fin.castAdd b jL) =
              Fin.castAdd (b + 1) (⟨jL, hlt⟩ : Fin a) := by
          ext
          simp
        rw [hcast, Fin.append_left, Fin.init_def]
        congr 1
    · rw [Fin.append_right]
      have hcast :
          Fin.cast (by omega) (Fin.natAdd (a + 1) jR) =
            Fin.natAdd a (jR.succ) := by
        ext
        simp
        omega
      rw [hcast, Fin.append_right, Fin.tail_def]
  rw [hsource]
  congr 1

omit [Fintype Ω] [DecidableEq Ω] in
/-- Path weights multiply under the tail-based two-path glue. -/
theorem pathWeight_openPathGlue (M : Matrix Ω Ω ℝ) {a b : ℕ}
    (σ : Fin (a + 1) → Ω) (τ : Fin (b + 1) → Ω)
    (hστ : σ (Fin.last a) = τ 0) :
    pathWeight M (openPathGlue σ τ) = pathWeight M σ * pathWeight M τ := by
  rw [openPathGlue_eq_append_init σ τ hστ]
  convert pathWeight_append M σ τ hστ.symm using 1

omit [Fintype Ω] [DecidableEq Ω] in
/-- The final point of a glued two-path open path is the final point of the
second path. -/
theorem openPathGlue_apply_last {a b : ℕ}
    (σ : Fin (a + 1) → Ω) (τ : Fin (b + 1) → Ω)
    (hστ : σ (Fin.last a) = τ 0) :
    openPathGlue σ τ (Fin.last (a + b)) = τ (Fin.last b) := by
  by_cases hb : b = 0
  · subst hb
    unfold openPathGlue
    have hidx :
        Fin.cast (by omega) (Fin.last (a + 0)) =
          Fin.castAdd 0 (Fin.last a : Fin (a + 1)) := by
      ext
      simp
    rw [hidx, Fin.append_left, hστ]
    rfl
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
    unfold openPathGlue
    have hidx :
        Fin.cast (by omega) (Fin.last (a + (m + 1))) =
          Fin.natAdd (a + 1) (Fin.last m) := by
      ext
      simp
    rw [hidx, Fin.append_right, Fin.tail_def]
    rfl

/-- Glue three open paths into one open path, keeping the two shared endpoints
only once.  The constraints are supplied to the lemmas using this map, rather
than to the definition itself. -/
def openMarkedTripleGlue {left sep right : ℕ}
    (σ : Fin (left + 1) → Ω) (τ : Fin (sep + 1) → Ω)
    (ρ : Fin (right + 1) → Ω) : Fin (left + sep + right + 1) → Ω :=
  openPathGlue (openPathGlue σ τ) ρ

omit [Fintype Ω] [DecidableEq Ω] in
/-- The glued open path starts at the first path. -/
theorem openMarkedTripleGlue_apply_zero {left sep right : ℕ}
    (σ : Fin (left + 1) → Ω) (τ : Fin (sep + 1) → Ω)
    (ρ : Fin (right + 1) → Ω) :
    openMarkedTripleGlue σ τ ρ 0 = σ 0 := by
  unfold openMarkedTripleGlue
  rw [openPathGlue_apply_zero, openPathGlue_apply_zero]

omit [Fintype Ω] [DecidableEq Ω] in
/-- The left marked position of the glued open path is the join of the first
and middle paths. -/
theorem openMarkedTripleGlue_apply_left {left sep right : ℕ}
    (σ : Fin (left + 1) → Ω) (τ : Fin (sep + 1) → Ω)
    (ρ : Fin (right + 1) → Ω) :
    openMarkedTripleGlue σ τ ρ (layerOpenLeftIndex left sep right) =
      σ (Fin.last left) := by
  have hidx :
      (layerOpenLeftIndex left sep right : Fin (left + sep + right + 1)) =
        ⟨left, by omega⟩ := by
    ext
    simp [layerOpenLeftIndex]
  unfold openMarkedTripleGlue
  rw [hidx]
  unfold openPathGlue
  have houter :
      Fin.cast (by omega) (⟨left, by omega⟩ : Fin (left + sep + right + 1)) =
        Fin.castAdd right (⟨left, by omega⟩ : Fin (left + sep + 1)) := by
    ext
    simp
  have hinner :
      Fin.cast (by omega) (⟨left, by omega⟩ : Fin (left + sep + 1)) =
        Fin.castAdd sep (Fin.last left) := by
    ext
    simp
  rw [houter, Fin.append_left, hinner, Fin.append_left]

omit [Fintype Ω] [DecidableEq Ω] in
/-- The right marked position of the glued open path is the join of the middle
and final paths. -/
theorem openMarkedTripleGlue_apply_right {left sep right : ℕ}
    (σ : Fin (left + 1) → Ω) (τ : Fin (sep + 1) → Ω)
    (ρ : Fin (right + 1) → Ω)
    (hστ : σ (Fin.last left) = τ 0) :
    openMarkedTripleGlue σ τ ρ (layerOpenRightIndex left sep right) =
      τ (Fin.last sep) := by
  by_cases hsep : sep = 0
  · subst hsep
    have hidx :
        layerOpenRightIndex left 0 right = layerOpenLeftIndex left 0 right := by
      ext
      simp [layerOpenRightIndex, layerOpenLeftIndex]
    rw [hidx, openMarkedTripleGlue_apply_left, hστ]
    rfl
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hsep
    have hidx :
        (layerOpenRightIndex left (m + 1) right :
          Fin (left + (m + 1) + right + 1)) =
          ⟨left + (m + 1), by omega⟩ := by
      ext
      simp [layerOpenRightIndex]
    unfold openMarkedTripleGlue
    rw [hidx, openPathGlue_apply_first_last,
      openPathGlue_apply_last σ τ hστ]

/-- The left segment of a single open marked path. -/
def openMarkedTripleLeft {left sep right : ℕ}
    (c : Fin (left + sep + right + 1) → Ω) : Fin (left + 1) → Ω :=
  fun i => c (Fin.cast (by omega) (Fin.castAdd (sep + right) i))

/-- The middle segment of a single open marked path. -/
def openMarkedTripleMiddle {left sep right : ℕ}
    (c : Fin (left + sep + right + 1) → Ω) : Fin (sep + 1) → Ω :=
  fun i => c (Fin.cast (by omega) (Fin.natAdd left (Fin.castAdd right i)))

/-- The right segment of a single open marked path. -/
def openMarkedTripleRight {left sep right : ℕ}
    (c : Fin (left + sep + right + 1) → Ω) : Fin (right + 1) → Ω :=
  fun i => c (Fin.cast (by omega) (Fin.natAdd (left + sep) i))

omit [Fintype Ω] [DecidableEq Ω] in
/-- The left and middle segments reconstructed from a single path glue at the
left marked point. -/
theorem openMarkedTripleLeft_last_eq_middle_zero {left sep right : ℕ}
    (c : Fin (left + sep + right + 1) → Ω) :
    openMarkedTripleLeft c (Fin.last left) = openMarkedTripleMiddle c 0 := by
  unfold openMarkedTripleLeft openMarkedTripleMiddle
  congr 1

omit [Fintype Ω] [DecidableEq Ω] in
/-- The middle and right segments reconstructed from a single path glue at the
right marked point. -/
theorem openMarkedTripleMiddle_last_eq_right_zero {left sep right : ℕ}
    (c : Fin (left + sep + right + 1) → Ω) :
    openMarkedTripleMiddle c (Fin.last sep) = openMarkedTripleRight c 0 := by
  unfold openMarkedTripleMiddle openMarkedTripleRight
  congr 1

omit [Fintype Ω] [DecidableEq Ω] in
/-- Splitting a glued triple recovers the left path. -/
theorem openMarkedTripleLeft_glue {left sep right : ℕ}
    (σ : Fin (left + 1) → Ω) (τ : Fin (sep + 1) → Ω)
    (ρ : Fin (right + 1) → Ω) :
    openMarkedTripleLeft (openMarkedTripleGlue σ τ ρ) = σ := by
  funext i
  unfold openMarkedTripleLeft openMarkedTripleGlue
  have houter :
      (Fin.cast (by omega) (Fin.castAdd (sep + right) i) :
          Fin (left + sep + right + 1)) =
        Fin.cast (by omega)
          (Fin.castAdd right
            (Fin.cast (by omega) (Fin.castAdd sep i) : Fin (left + sep + 1))) := by
    ext
    simp
  rw [houter, openPathGlue_apply_left, openPathGlue_apply_left]

omit [Fintype Ω] [DecidableEq Ω] in
/-- Splitting a glued triple recovers the middle path, provided the left join is
valid. -/
theorem openMarkedTripleMiddle_glue {left sep right : ℕ}
    (σ : Fin (left + 1) → Ω) (τ : Fin (sep + 1) → Ω)
    (ρ : Fin (right + 1) → Ω)
    (hστ : σ (Fin.last left) = τ 0) :
    openMarkedTripleMiddle (openMarkedTripleGlue σ τ ρ) = τ := by
  funext i
  refine Fin.cases ?_ ?_ i
  · unfold openMarkedTripleMiddle openMarkedTripleGlue
    have houter :
        (Fin.cast (by omega)
            (Fin.natAdd left (Fin.castAdd right (0 : Fin (sep + 1)))) :
            Fin (left + sep + right + 1)) =
          Fin.cast (by omega)
            (Fin.castAdd right (⟨left, by omega⟩ : Fin (left + sep + 1))) := by
      ext
      simp
    rw [houter, openPathGlue_apply_left, openPathGlue_apply_first_last, hστ]
  · intro j
    unfold openMarkedTripleMiddle openMarkedTripleGlue
    have houter :
        (Fin.cast (by omega) (Fin.natAdd left (Fin.castAdd right j.succ)) :
            Fin (left + sep + right + 1)) =
          Fin.cast (by omega)
            (Fin.castAdd right
              (Fin.cast (by omega) (Fin.natAdd (left + 1) j) :
                Fin (left + sep + 1))) := by
      ext
      simp
      omega
    rw [houter, openPathGlue_apply_left, openPathGlue_apply_right_succ]

omit [Fintype Ω] [DecidableEq Ω] in
/-- Splitting a glued triple recovers the right path, provided both joins are
valid. -/
theorem openMarkedTripleRight_glue {left sep right : ℕ}
    (σ : Fin (left + 1) → Ω) (τ : Fin (sep + 1) → Ω)
    (ρ : Fin (right + 1) → Ω)
    (hστ : σ (Fin.last left) = τ 0)
    (hτρ : τ (Fin.last sep) = ρ 0) :
    openMarkedTripleRight (openMarkedTripleGlue σ τ ρ) = ρ := by
  funext i
  refine Fin.cases ?_ ?_ i
  · unfold openMarkedTripleRight openMarkedTripleGlue
    have hidx :
        (Fin.cast (by omega) (Fin.natAdd (left + sep) (0 : Fin (right + 1))) :
            Fin (left + sep + right + 1)) =
          ⟨left + sep, by omega⟩ := by
      ext
      simp
    rw [hidx, openPathGlue_apply_first_last, openPathGlue_apply_last σ τ hστ, hτρ]
  · intro j
    unfold openMarkedTripleRight openMarkedTripleGlue
    have hidx :
        (Fin.cast (by omega) (Fin.natAdd (left + sep) j.succ) :
            Fin (left + sep + right + 1)) =
          Fin.cast (by omega) (Fin.natAdd (left + sep + 1) j) := by
      ext
      simp
      omega
    rw [hidx, openPathGlue_apply_right_succ]

omit [Fintype Ω] [DecidableEq Ω] in
/-- Gluing the three segments split from a single open marked path recovers the
original path. -/
theorem openMarkedTripleGlue_split {left sep right : ℕ}
    (c : Fin (left + sep + right + 1) → Ω) :
    openMarkedTripleGlue
        (openMarkedTripleLeft c) (openMarkedTripleMiddle c) (openMarkedTripleRight c) = c := by
  unfold openMarkedTripleGlue
  have hleft :
      openMarkedTripleLeft c =
        openPathGlueLeft (a := left) (b := sep)
          (openPathGlueLeft (a := left + sep) (b := right) c) := by
    funext i
    unfold openMarkedTripleLeft openPathGlueLeft
    apply congrArg c
    ext
    simp
  have hmiddle :
      openMarkedTripleMiddle c =
        openPathGlueRight (a := left) (b := sep)
          (openPathGlueLeft (a := left + sep) (b := right) c) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · unfold openMarkedTripleMiddle openPathGlueRight openPathGlueLeft
      simp only [Fin.cases_zero]
      apply congrArg c
      ext
      simp
    · intro j
      unfold openMarkedTripleMiddle openPathGlueRight openPathGlueLeft
      simp only [Fin.cases_succ]
      apply congrArg c
      ext
      simp
      omega
  have hright :
      openMarkedTripleRight c =
        openPathGlueRight (a := left + sep) (b := right) c := by
    funext i
    refine Fin.cases ?_ ?_ i
    · unfold openMarkedTripleRight openPathGlueRight
      simp only [Fin.cases_zero]
      apply congrArg c
      ext
      simp
    · intro j
      unfold openMarkedTripleRight openPathGlueRight
      simp only [Fin.cases_succ]
      apply congrArg c
      ext
      simp
      omega
  rw [hleft, hmiddle, openPathGlue_split, hright, openPathGlue_split]

omit [Fintype Ω] [DecidableEq Ω] in
/-- The three-path glue is the iterated two-path glue. -/
theorem openMarkedTripleGlue_eq_openPathGlue {left sep right : ℕ}
    (σ : Fin (left + 1) → Ω) (τ : Fin (sep + 1) → Ω)
    (ρ : Fin (right + 1) → Ω) :
    openMarkedTripleGlue σ τ ρ = openPathGlue (openPathGlue σ τ) ρ := by
  rfl

omit [Fintype Ω] [DecidableEq Ω] in
/-- Path weights multiply under the three-path glue. -/
theorem pathWeight_openMarkedTripleGlue (M : Matrix Ω Ω ℝ) {left sep right : ℕ}
    (σ : Fin (left + 1) → Ω) (τ : Fin (sep + 1) → Ω)
    (ρ : Fin (right + 1) → Ω)
    (hστ : σ (Fin.last left) = τ 0)
    (hτρ : τ (Fin.last sep) = ρ 0) :
    pathWeight M (openMarkedTripleGlue σ τ ρ) =
      pathWeight M σ * pathWeight M τ * pathWeight M ρ := by
  rw [openMarkedTripleGlue_eq_openPathGlue]
  have hmid : openPathGlue σ τ (Fin.last (left + sep)) = ρ 0 := by
    rw [openPathGlue_apply_last σ τ hστ, hτρ]
  rw [pathWeight_openPathGlue M (openPathGlue σ τ) ρ hmid,
    pathWeight_openPathGlue M σ τ hστ]

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
