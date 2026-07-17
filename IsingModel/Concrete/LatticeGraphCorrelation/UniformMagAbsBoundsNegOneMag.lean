import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `neg_one_le_magnetization*_latticeGraph` wrappers

Narrow child module for three ℤ^d `neg_one_le_magnetization*_latticeGraph`
wrappers (Λ / AlongExhaustion / Infinite forms) extracted from
`UniformMagAbsBoundsSqAndNegOneMag.lean`:

* `neg_one_le_magnetizationΛ_latticeGraph`,
* `neg_one_le_magnetizationAlongExhaustion_latticeGraph`,
* `neg_one_le_magnetizationInfinite_latticeGraph`.

Each result is a thin pass-through of the ambient
`Ambient.neg_one_le_magnetization*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `UniformMagAbsBoundsSqAndNegOneMag` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `-1 ≤ magnetizationΛ`**. -/
theorem neg_one_le_magnetizationΛ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (i : ↑Λ) :
    -1 ≤ magnetizationΛ (IsingModel.latticeGraph d) Λ p i :=
  neg_one_le_magnetizationΛ (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `-1 ≤ magnetizationAlongExhaustion`** per stage. -/
theorem neg_one_le_magnetizationAlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    -1 ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n :=
  neg_one_le_magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n

/-- **ℤ^d `-1 ≤ magnetizationInfinite`** (unconditional). -/
theorem neg_one_le_magnetizationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    -1 ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ p i :=
  neg_one_le_magnetizationInfinite (IsingModel.latticeGraph d) Λ p i

end Ambient
end IsingModel
