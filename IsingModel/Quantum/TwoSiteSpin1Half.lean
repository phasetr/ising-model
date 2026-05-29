import IsingModel.Quantum.SingleSpin
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Two-site spin-1/2 quantum system (Tasaki Ch 2.2)

This file begins the formalisation of Tasaki §2.2 (quantum spin systems on a
lattice) at the simplest non-trivial case: two spin-1/2 sites, indexed by
`Fin 2`. The single-site Hilbert space is `ℂ² ≃ Matrix (Fin 2) (Fin 2) ℂ` from
`SingleSpin.lean` (Tasaki §2.1).

The two-site Hilbert space is the tensor product `h₀ ⊗ h₀`, and operators are
elements of `End (h₀ ⊗ h₀) = Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ` via the
Kronecker product `Matrix.kronecker`. A site-local spin operator `S^(α)_x`
extends the single-site `S^(α)` to act non-trivially only on site `x`:

* `S^(α)_0 = S^(α) ⊗ I` (site 0 acts, site 1 is identity).
* `S^(α)_1 = I ⊗ S^(α)` (site 1 acts, site 0 is identity).

The total spin operator is `S^(α)_tot = S^(α)_0 + S^(α)_1` (Tasaki 2.2.8).

This file defines the four site-local spin-1/2 operators (X, Y, Z at sites 0
and 1) and the total spin operators, and proves the basic commutation
`[S^(α)_0, S^(β)_1] = 0` (operators on different sites commute, Tasaki §2.2).

References:

* H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, GTP,
  Springer 2020, §2.2 (Quantum Spin Systems), pp. 21-25.
-/

namespace IsingModel.Quantum

open Complex Matrix

/-- The 2×2 identity matrix on a single spin-1/2 site (`Matrix (Fin 2) (Fin 2) ℂ`). -/
def IdSpin1Half : Matrix (Fin 2) (Fin 2) ℂ := 1

/-- Site-0 X-spin operator `S^(1)_0 = S^(1) ⊗ I` in the two-site system. -/
noncomputable def spinOp1Half_x_site0 :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker spinOp1Half_x IdSpin1Half

/-- Site-0 Y-spin operator `S^(2)_0 = S^(2) ⊗ I` in the two-site system. -/
noncomputable def spinOp1Half_y_site0 :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker spinOp1Half_y IdSpin1Half

/-- Site-0 Z-spin operator `S^(3)_0 = S^(3) ⊗ I` in the two-site system. -/
noncomputable def spinOp1Half_z_site0 :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker spinOp1Half_z IdSpin1Half

/-- Site-1 X-spin operator `S^(1)_1 = I ⊗ S^(1)` in the two-site system. -/
noncomputable def spinOp1Half_x_site1 :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker IdSpin1Half spinOp1Half_x

/-- Site-1 Y-spin operator `S^(2)_1 = I ⊗ S^(2)` in the two-site system. -/
noncomputable def spinOp1Half_y_site1 :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker IdSpin1Half spinOp1Half_y

/-- Site-1 Z-spin operator `S^(3)_1 = I ⊗ S^(3)` in the two-site system. -/
noncomputable def spinOp1Half_z_site1 :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker IdSpin1Half spinOp1Half_z

/-- Total X-spin operator `S^(1)_tot = S^(1)_0 + S^(1)_1` (Tasaki 2.2.8). -/
noncomputable def spinOp1Half_x_total :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  spinOp1Half_x_site0 + spinOp1Half_x_site1

/-- Total Y-spin operator `S^(2)_tot = S^(2)_0 + S^(2)_1` (Tasaki 2.2.8). -/
noncomputable def spinOp1Half_y_total :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  spinOp1Half_y_site0 + spinOp1Half_y_site1

/-- Total Z-spin operator `S^(3)_tot = S^(3)_0 + S^(3)_1` (Tasaki 2.2.8). -/
noncomputable def spinOp1Half_z_total :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  spinOp1Half_z_site0 + spinOp1Half_z_site1

/-- **Generic cross-tensor commutativity**: `(A ⊗ I) · (I ⊗ B) = (I ⊗ B) · (A ⊗ I)`
for any pair of square matrices `A`, `B` on the same dimension `Fin 2`.

Both sides equal `A ⊗ B` via `Matrix.mul_kronecker_mul` plus `mul_one` /
`one_mul`. This is the fundamental observation underlying the locality of
quantum spin systems: operators acting on different tensor factors commute,
regardless of which factor and which operators they involve. -/
theorem kronecker_one_commute (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.kronecker A (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) B =
      Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) B *
        Matrix.kronecker A (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [show Matrix.kronecker A (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) B =
        Matrix.kronecker (A * 1) (1 * B) from
        (Matrix.mul_kronecker_mul _ _ _ _).symm]
  rw [show Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) B *
        Matrix.kronecker A (1 : Matrix (Fin 2) (Fin 2) ℂ) =
        Matrix.kronecker (1 * A) (B * 1) from
        (Matrix.mul_kronecker_mul _ _ _ _).symm]
  simp

/-- **Cross-site spin operators commute** (XX pair): `[S^(1)_0, S^(1)_1] = 0`. -/
theorem spinOp1Half_x_site0_commute_x_site1 :
    spinOp1Half_x_site0 * spinOp1Half_x_site1 =
      spinOp1Half_x_site1 * spinOp1Half_x_site0 := by
  unfold spinOp1Half_x_site0 spinOp1Half_x_site1 IdSpin1Half
  exact kronecker_one_commute _ _

/-- Cross-site commutativity for `(α, β) = (1, 2)`: `[S^(1)_0, S^(2)_1] = 0`. -/
theorem spinOp1Half_x_site0_commute_y_site1 :
    spinOp1Half_x_site0 * spinOp1Half_y_site1 =
      spinOp1Half_y_site1 * spinOp1Half_x_site0 := by
  unfold spinOp1Half_x_site0 spinOp1Half_y_site1 IdSpin1Half
  exact kronecker_one_commute _ _

/-- Cross-site commutativity for `(α, β) = (1, 3)`: `[S^(1)_0, S^(3)_1] = 0`. -/
theorem spinOp1Half_x_site0_commute_z_site1 :
    spinOp1Half_x_site0 * spinOp1Half_z_site1 =
      spinOp1Half_z_site1 * spinOp1Half_x_site0 := by
  unfold spinOp1Half_x_site0 spinOp1Half_z_site1 IdSpin1Half
  exact kronecker_one_commute _ _

/-- Cross-site commutativity for `(α, β) = (2, 1)`: `[S^(2)_0, S^(1)_1] = 0`. -/
theorem spinOp1Half_y_site0_commute_x_site1 :
    spinOp1Half_y_site0 * spinOp1Half_x_site1 =
      spinOp1Half_x_site1 * spinOp1Half_y_site0 := by
  unfold spinOp1Half_y_site0 spinOp1Half_x_site1 IdSpin1Half
  exact kronecker_one_commute _ _

/-- Cross-site commutativity for `(α, β) = (2, 2)`: `[S^(2)_0, S^(2)_1] = 0`. -/
theorem spinOp1Half_y_site0_commute_y_site1 :
    spinOp1Half_y_site0 * spinOp1Half_y_site1 =
      spinOp1Half_y_site1 * spinOp1Half_y_site0 := by
  unfold spinOp1Half_y_site0 spinOp1Half_y_site1 IdSpin1Half
  exact kronecker_one_commute _ _

/-- Cross-site commutativity for `(α, β) = (2, 3)`: `[S^(2)_0, S^(3)_1] = 0`. -/
theorem spinOp1Half_y_site0_commute_z_site1 :
    spinOp1Half_y_site0 * spinOp1Half_z_site1 =
      spinOp1Half_z_site1 * spinOp1Half_y_site0 := by
  unfold spinOp1Half_y_site0 spinOp1Half_z_site1 IdSpin1Half
  exact kronecker_one_commute _ _

/-- Cross-site commutativity for `(α, β) = (3, 1)`: `[S^(3)_0, S^(1)_1] = 0`. -/
theorem spinOp1Half_z_site0_commute_x_site1 :
    spinOp1Half_z_site0 * spinOp1Half_x_site1 =
      spinOp1Half_x_site1 * spinOp1Half_z_site0 := by
  unfold spinOp1Half_z_site0 spinOp1Half_x_site1 IdSpin1Half
  exact kronecker_one_commute _ _

/-- Cross-site commutativity for `(α, β) = (3, 2)`: `[S^(3)_0, S^(2)_1] = 0`. -/
theorem spinOp1Half_z_site0_commute_y_site1 :
    spinOp1Half_z_site0 * spinOp1Half_y_site1 =
      spinOp1Half_y_site1 * spinOp1Half_z_site0 := by
  unfold spinOp1Half_z_site0 spinOp1Half_y_site1 IdSpin1Half
  exact kronecker_one_commute _ _

/-- Cross-site commutativity for `(α, β) = (3, 3)`: `[S^(3)_0, S^(3)_1] = 0`. -/
theorem spinOp1Half_z_site0_commute_z_site1 :
    spinOp1Half_z_site0 * spinOp1Half_z_site1 =
      spinOp1Half_z_site1 * spinOp1Half_z_site0 := by
  unfold spinOp1Half_z_site0 spinOp1Half_z_site1 IdSpin1Half
  exact kronecker_one_commute _ _

/-- **The spin-spin dot product** `S_0 · S_1 := ∑_α S^(α)_0 · S^(α)_1` for the
two-site spin-1/2 system (Tasaki §2.2). This is the building block of the
Heisenberg Hamiltonian (Tasaki 2.4 / 2.5). -/
noncomputable def spinDotProduct1Half_01 :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  spinOp1Half_x_site0 * spinOp1Half_x_site1 +
  spinOp1Half_y_site0 * spinOp1Half_y_site1 +
  spinOp1Half_z_site0 * spinOp1Half_z_site1

/-- **Symmetry of the spin-spin dot product** under site swap: `S_0 · S_1 = S_1 · S_0`
(at the 2-site spin-1/2 case). Follows from cross-site commutativity. -/
theorem spinDotProduct1Half_01_symm :
    spinDotProduct1Half_01 =
      spinOp1Half_x_site1 * spinOp1Half_x_site0 +
      spinOp1Half_y_site1 * spinOp1Half_y_site0 +
      spinOp1Half_z_site1 * spinOp1Half_z_site0 := by
  unfold spinDotProduct1Half_01
  rw [spinOp1Half_x_site0_commute_x_site1,
      spinOp1Half_y_site0_commute_y_site1,
      spinOp1Half_z_site0_commute_z_site1]

end IsingModel.Quantum
