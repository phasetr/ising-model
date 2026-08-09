import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d fixed-volume pair correlation bounds at zero field

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ` and at the parameter
record `⟨J, 0, β⟩`, the nonnegativity of the pair correlation `⟨σ_i σ_j⟩` and its upper bound
`1`. Nonnegativity assumes `0 ≤ β * J`; the upper bound holds with no condition on `J`, `β`,
`Λ` or the sites.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Λ-level pair correlation nonneg at h = 0**:
under `0 ≤ β·J`, `0 ≤ correlationΛ (latticeGraph d) Λ ⟨J, 0, β⟩ {i, j}`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    0 ≤ correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) :=
  correlationΛ_high_temp_h_zero_at_pair_nonneg
    (IsingModel.latticeGraph d) Λ J β hβJ i j

/-- **ℤ^d Λ-level pair correlation ≤ 1**:
`correlationΛ (latticeGraph d) Λ ⟨J, 0, β⟩ {i, j} ≤ 1`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 :=
  correlationΛ_high_temp_h_zero_at_pair_le_one
    (IsingModel.latticeGraph d) Λ J β i j

end Ambient

end IsingModel
