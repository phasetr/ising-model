import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d truncated{2,3,4}Infinite exhaustion-independence wrappers

Narrow child module for three ℤ^d
`truncated{2,3,4}Infinite_latticeGraph_indep_exhaustion` wrappers extracted
from `TwoPointTruncatedHigher.lean`. Each wrapper is a thin pass-through to
the corresponding ambient lemma at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d truncated2Infinite exhaustion-independence**. -/
theorem truncated2Infinite_latticeGraph_indep_exhaustion
    (d : ℕ) (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ p i j
      = truncated2Infinite (IsingModel.latticeGraph d) Λ' p i j :=
  truncated2Infinite_indep_exhaustion (IsingModel.latticeGraph d) Λ Λ' p hf i j

/-- **ℤ^d truncated3Infinite exhaustion-independence**. -/
theorem truncated3Infinite_latticeGraph_indep_exhaustion
    (d : ℕ) (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ p i j k
      = truncated3Infinite (IsingModel.latticeGraph d) Λ' p i j k :=
  truncated3Infinite_indep_exhaustion (IsingModel.latticeGraph d) Λ Λ' p hf i j k

/-- **ℤ^d truncated4Infinite exhaustion-independence**. -/
theorem truncated4Infinite_latticeGraph_indep_exhaustion
    (d : ℕ) (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ p i j k l
      = truncated4Infinite (IsingModel.latticeGraph d) Λ' p i j k l :=
  truncated4Infinite_indep_exhaustion (IsingModel.latticeGraph d) Λ Λ' p hf
    i j k l

end Ambient
end IsingModel
