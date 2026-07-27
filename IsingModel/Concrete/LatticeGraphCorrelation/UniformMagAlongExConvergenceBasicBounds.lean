import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d magnetizationAlongEx basic per-stage bound wrappers

Narrow child module for three ℤ^d basic per-stage
`magnetizationAlongExhaustion_latticeGraph_*` bound wrappers:

* `magnetizationAlongExhaustion_latticeGraph_le_one`,
* `magnetizationAlongExhaustion_latticeGraph_nonneg`,
* `magnetizationAlongExhaustion_latticeGraph_le_magnetizationInfinite`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d magnetizationAlongExhaustion ≤ 1** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n ≤ 1 :=
  magnetizationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ p i n

/-- **ℤ^d magnetizationAlongExhaustion ≥ 0** per stage (ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) (n : ℕ) :
    0 ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n :=
  magnetizationAlongExhaustion_nonneg (IsingModel.latticeGraph d) Λ p hf i n

/-- **ℤ^d `magnetizationAlongExhaustion ≤ magnetizationInfinite`** per stage
(ferromagnetic): stage-wise upper bound by the limsup value. -/
theorem magnetizationAlongExhaustion_latticeGraph_le_magnetizationInfinite
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ p i :=
  magnetizationAlongExhaustion_le_magnetizationInfinite
    (IsingModel.latticeGraph d) Λ p i n

end Ambient
end IsingModel
