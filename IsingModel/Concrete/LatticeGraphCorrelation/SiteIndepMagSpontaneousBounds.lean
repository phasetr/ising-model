import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Range of the ℤ^d spontaneous magnetization

Concrete `IsingModel.latticeGraph d` statements at an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and at an arbitrary site. The spontaneous magnetization is bounded below by
`-1`, bounded above by `1`, and bounded in absolute value by `1`; it is moreover
non-negative, which sharpens the lower bound. Every statement assumes a non-negative
coupling and a positive inverse temperature, and none takes an instance argument.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d `-1 ≤ spontaneousMagnetization`** (ferromagnetic). -/
theorem neg_one_le_spontaneousMagnetization_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    -1 ≤ spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i :=
  neg_one_le_spontaneousMagnetization (IsingModel.latticeGraph d) Λ hJ hβ i

/-- **ℤ^d `|spontaneousMagnetization| ≤ 1`** (ferromagnetic). -/
theorem abs_spontaneousMagnetization_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    |spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i| ≤ 1 :=
  abs_spontaneousMagnetization_le_one (IsingModel.latticeGraph d) Λ hJ hβ i

/-- **ℤ^d spontaneousMagnetization ≥ 0** (ferromagnetic). -/
theorem spontaneousMagnetization_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    0 ≤ spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i :=
  spontaneousMagnetization_nonneg (IsingModel.latticeGraph d) Λ hJ hβ i

/-- **ℤ^d spontaneousMagnetization ≤ 1** (ferromagnetic). -/
theorem spontaneousMagnetization_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i ≤ 1 :=
  spontaneousMagnetization_le_one (IsingModel.latticeGraph d) Λ hJ hβ i

end Ambient

end IsingModel
