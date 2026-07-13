import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.PhaseTransition

/-!
# ℤ^d uniformSpontaneousMagnetization bound wrappers

Narrow child module for five ℤ^d uniform-spontaneous-magnetization bound
wrappers extracted from `SiteIndepMagUniformSpontaneous.lean`:

* `uniformSpontaneousMagnetization_nonneg`,
* `uniformSpontaneousMagnetization_le_one`,
* `neg_one_le_uniformSpontaneousMagnetization`,
* `abs_uniformSpontaneousMagnetization_le_one`,
* `uniformSpontaneousMagnetization_sq_le_one`.
-/

namespace IsingModel
namespace Ambient

/-- **Nonnegativity of `uniformSpontaneousMagnetization`**. -/
theorem uniformSpontaneousMagnetization_nonneg
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    0 ≤ uniformSpontaneousMagnetization d J β :=
  spontaneousMagnetization_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ 0

/-- **Upper bound on `uniformSpontaneousMagnetization`**:
`uniformSpontaneousMagnetization d J β ≤ 1`. -/
theorem uniformSpontaneousMagnetization_le_one
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    uniformSpontaneousMagnetization d J β ≤ 1 :=
  spontaneousMagnetization_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ 0

/-- **`-1 ≤ uniformSpontaneousMagnetization`** (ferromagnetic).
Direct from `uniformSpontaneousMagnetization_nonneg`. -/
theorem neg_one_le_uniformSpontaneousMagnetization
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    -1 ≤ uniformSpontaneousMagnetization d J β := by
  have := uniformSpontaneousMagnetization_nonneg d hJ hβ
  linarith

/-- **`|uniformSpontaneousMagnetization| ≤ 1`** (ferromagnetic). -/
theorem abs_uniformSpontaneousMagnetization_le_one
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    |uniformSpontaneousMagnetization d J β| ≤ 1 :=
  abs_le.mpr ⟨neg_one_le_uniformSpontaneousMagnetization d hJ hβ,
    uniformSpontaneousMagnetization_le_one d hJ hβ⟩

/-- **`uniformSpontaneousMagnetization² ≤ 1`** (ferromagnetic). -/
theorem uniformSpontaneousMagnetization_sq_le_one
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    uniformSpontaneousMagnetization d J β ^ 2 ≤ 1 :=
  spontaneousMagnetization_sq_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ 0

end Ambient
end IsingModel
