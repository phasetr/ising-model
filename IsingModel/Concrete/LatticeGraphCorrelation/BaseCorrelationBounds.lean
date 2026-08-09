import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d finite-volume partition-function positivity and correlation range

Concrete `IsingModel.latticeGraph d` statements at a fixed finite subset of `Fin d → ℤ`
and an unrestricted parameter record.

The partition function of the finite volume is strictly positive, and the correlation of a
site set of that volume is at most `1` in absolute value. The one-sided bound by `1` is
taken directly from the ambient statement. Those statements take no hypothesis.
Non-negativity of the same correlation is the one statement here that assumes
`Ferromagnetic` on the parameter record, and it is the finite-volume form of the first
Griffiths-Kelly-Sherman inequality. No instance argument is taken.
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
