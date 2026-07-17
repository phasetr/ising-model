import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d correlationΛ / partitionFunctionΛ basic bound wrappers

Narrow child module for four ℤ^d basic Λ-direct bound wrappers
extracted from `Base.lean`:

* `partitionFunctionΛ_latticeGraph_pos`,
* `abs_correlationΛ_latticeGraph_le_one`,
* `correlationΛ_latticeGraph_le_one`,
* `correlationΛ_latticeGraph_nonneg`.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d partitionFunctionΛ positivity** per finite volume. -/
theorem partitionFunctionΛ_latticeGraph_pos
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    0 < partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_pos (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `|correlationΛ| ≤ 1`** per finite volume. -/
theorem abs_correlationΛ_latticeGraph_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    |correlationΛ (IsingModel.latticeGraph d) Λ p A| ≤ 1 :=
  abs_correlationΛ_le_one (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d correlationΛ ≤ 1** per finite volume. -/
theorem correlationΛ_latticeGraph_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ (IsingModel.latticeGraph d) Λ p A ≤ 1 :=
  correlationΛ_le_one (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d correlationΛ ≥ 0** per finite volume (ferromagnetic). -/
theorem correlationΛ_latticeGraph_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (A : Finset (↑Λ : Type _)) :
    0 ≤ correlationΛ (IsingModel.latticeGraph d) Λ p A :=
  correlationΛ_nonneg (IsingModel.latticeGraph d) Λ p hf A

end Ambient
end IsingModel
