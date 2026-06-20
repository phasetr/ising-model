import IsingModel.TransferMatrix.LayerDoobTransform

/-!
# Projective cross-ratio and its row/column scaling invariance

The Hilbert projective (Birkhoff) metric route to a uniform spectral gap is
governed by the **projective cross-ratio**
`crossRatio A i j a b = (A i a · A j b) / (A i b · A j a)`.
Its defining feature is invariance under positive **row and column scaling**
`A i j ↦ r i · A i j · c j`: every `r` and `c` factor cancels.

Two consequences isolate the gap-controlling quantity from the unknown Perron
data:

* the **balanced** layer transfer matrix `M a b = √(u a) · k a b · √(u b)` has the
  same cross-ratio as the bare transition kernel `k` (the `√u` factors cancel), so
  the projective geometry depends only on `k`, not on the layer weight `u`;
* the **Doob transform** `P i j = M i j · w j / (λ · w i)` has the same cross-ratio
  as `M` (the Perron vector `w` and eigenvalue `λ` cancel).

Hence the cross-ratio of the Doob matrix equals that of `k` alone — independent of
both `u` and the Perron vector `w`.  This is route-independent infrastructure for
any later Hilbert-metric / Birkhoff--Hopf contraction argument; the contraction
theorem `δ ≤ tanh(Δ/4)` and the (subtle, tensorized) uniform high-temperature
estimate are **not** proved here, and the raw global projective diameter is **not**
claimed to be uniformly small.

The results are finite algebraic identities.  They do not bound the Dobrushin
coefficient, give a transverse-volume-uniform gap, prove a thermodynamic limit, or
prove final hyperplane exponential decay.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Section 17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The projective cross-ratio `(A i a · A j b) / (A i b · A j a)`. -/
noncomputable def matrixProjectiveCrossRatio (A : Matrix Ω Ω ℝ) (i j a b : Ω) : ℝ :=
  A i a * A j b / (A i b * A j a)

/-- **Row/column scaling invariance.**  Scaling a positive matrix by positive row
factors `r` and column factors `c` leaves the projective cross-ratio unchanged. -/
theorem matrixProjectiveCrossRatio_rowColScale {A : Matrix Ω Ω ℝ}
    (hA : MatrixEntrywisePositive A) {r c : Ω → ℝ}
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) (i j a b : Ω) :
    matrixProjectiveCrossRatio (fun i j => r i * A i j * c j) i j a b
      = matrixProjectiveCrossRatio A i j a b := by
  simp only [matrixProjectiveCrossRatio]
  have hia := (hA i a).ne'
  have hjb := (hA j b).ne'
  have hib := (hA i b).ne'
  have hja := (hA j a).ne'
  have hri := (hr i).ne'
  have hrj := (hr j).ne'
  have hca := (hc a).ne'
  have hcb := (hc b).ne'
  field_simp

/-- The balanced layer transfer matrix `M a b = √(u a) k a b √(u b)` has the same
projective cross-ratio as the bare transition kernel `k`: the `√u` factors
cancel. -/
theorem matrixProjectiveCrossRatio_layerSymmetricTransferMatrix
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} (hu : ∀ a, 0 < u a) (hk : MatrixEntrywisePositive k)
    (i j a b : Ω) :
    matrixProjectiveCrossRatio (layerSymmetricTransferMatrix u k) i j a b
      = matrixProjectiveCrossRatio k i j a b := by
  have hM : layerSymmetricTransferMatrix u k
      = fun i j => Real.sqrt (u i) * k i j * Real.sqrt (u j) := rfl
  rw [hM]
  exact matrixProjectiveCrossRatio_rowColScale hk
    (fun i => Real.sqrt_pos.mpr (hu i)) (fun j => Real.sqrt_pos.mpr (hu j)) i j a b

/-- The Doob transform `P i j = M i j w j / (λ w i)` has the same projective
cross-ratio as `M`: the Perron vector `w` and eigenvalue `λ` cancel. -/
theorem matrixProjectiveCrossRatio_matrixDoobTransform {M : Matrix Ω Ω ℝ}
    (hM : MatrixEntrywisePositive M) {lam : ℝ} (hlam : 0 < lam) {w : Ω → ℝ}
    (hw : VectorPositive w) (i j a b : Ω) :
    matrixProjectiveCrossRatio (matrixDoobTransform M lam w) i j a b
      = matrixProjectiveCrossRatio M i j a b := by
  have hP : matrixDoobTransform M lam w
      = fun i j => (1 / (lam * w i)) * M i j * w j := by
    funext i j; rw [matrixDoobTransform]; ring
  rw [hP]
  exact matrixProjectiveCrossRatio_rowColScale hM
    (fun i => by have := hw i; positivity) hw i j a b

/-- The Doob transform of the balanced layer transfer matrix has the same
projective cross-ratio as the bare transition kernel `k` — independent of both the
layer weight `u` and the Perron vector `w`. -/
theorem matrixProjectiveCrossRatio_matrixDoobTransform_layerSymmetricTransferMatrix
    {u : Ω → ℝ} {k : Ω → Ω → ℝ} (hu : ∀ a, 0 < u a) (hk : MatrixEntrywisePositive k)
    {lam : ℝ} (hlam : 0 < lam) {w : Ω → ℝ} (hw : VectorPositive w) (i j a b : Ω) :
    matrixProjectiveCrossRatio
        (matrixDoobTransform (layerSymmetricTransferMatrix u k) lam w) i j a b
      = matrixProjectiveCrossRatio k i j a b := by
  rw [matrixProjectiveCrossRatio_matrixDoobTransform
      (layerSymmetricTransferMatrix_entrywisePositive u k hu hk) hlam hw,
    matrixProjectiveCrossRatio_layerSymmetricTransferMatrix hu hk]

end TransferMatrix

end IsingModel
