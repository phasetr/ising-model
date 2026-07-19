import IsingModel.TransferMatrix.LayerOpenSlab

/-!
# Open-boundary layer path-glue infrastructure

Boundary-vector marked-numerator definitions and the open-path gluing/splitting
maps used to expand marked matrix-power numerators into glued open paths.

This is a build-speed split child of `LayerOpenSpectral`; see that umbrella
module for the mathematical overview and references.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Marked numerator matrix-power form -/

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

end TransferMatrix

end IsingModel
