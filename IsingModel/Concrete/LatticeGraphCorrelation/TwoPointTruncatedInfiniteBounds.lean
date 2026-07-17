import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d truncated2Infinite bound wrappers

Narrow child module for four ℤ^d `truncated2Infinite_latticeGraph_*`
bound wrappers (`le_one`, `neg_one_le`, `abs_le_one`, `sq_le_one`).
Each wrapper is a thin pass-through to the corresponding ambient
`truncated2Infinite_*` lemma at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `truncated2Infinite ≤ 1`** (ferromagnetic). -/
theorem truncated2Infinite_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ p i j ≤ 1 :=
  truncated2Infinite_le_one (IsingModel.latticeGraph d) Λ p hf i j

/-- **ℤ^d `-1 ≤ truncated2Infinite`** (ferromagnetic). -/
theorem neg_one_le_truncated2Infinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    -1 ≤ truncated2Infinite (IsingModel.latticeGraph d) Λ p i j :=
  neg_one_le_truncated2Infinite (IsingModel.latticeGraph d) Λ p hf i j

/-- **ℤ^d `|truncated2Infinite| ≤ 1`** (ferromagnetic). -/
theorem abs_truncated2Infinite_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    |truncated2Infinite (IsingModel.latticeGraph d) Λ p i j| ≤ 1 :=
  abs_truncated2Infinite_le_one (IsingModel.latticeGraph d) Λ p hf i j

/-- **ℤ^d `truncated2Infinite² ≤ 1`** (ferromagnetic). -/
theorem truncated2Infinite_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ p i j ^ 2 ≤ 1 :=
  truncated2Infinite_sq_le_one (IsingModel.latticeGraph d) Λ p hf i j

end Ambient
end IsingModel
