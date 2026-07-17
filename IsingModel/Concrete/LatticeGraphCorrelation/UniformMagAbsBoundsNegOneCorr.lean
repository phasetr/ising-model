import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `neg_one_le_correlation*_latticeGraph` wrappers

Narrow child module for three ℤ^d `neg_one_le_correlation*_latticeGraph`
wrappers (Λ / AlongExhaustion / Infinite forms) extracted from
`UniformMagAbsBounds.lean`:

* `neg_one_le_correlationΛ_latticeGraph`,
* `neg_one_le_correlationAlongExhaustion_latticeGraph`,
* `neg_one_le_correlationInfinite_latticeGraph`.

Each result is a thin pass-through of the ambient
`Ambient.neg_one_le_correlation*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `UniformMagAbsBounds` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `-1 ≤ correlationΛ`**. -/
theorem neg_one_le_correlationΛ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    -1 ≤ correlationΛ (IsingModel.latticeGraph d) Λ p A :=
  neg_one_le_correlationΛ (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `-1 ≤ correlationAlongExhaustion`** per stage. -/
theorem neg_one_le_correlationAlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    -1 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n :=
  neg_one_le_correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d `-1 ≤ correlationInfinite`** (unconditional). -/
theorem neg_one_le_correlationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    -1 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p A :=
  neg_one_le_correlationInfinite (IsingModel.latticeGraph d) Λ p A

end Ambient

end IsingModel
