import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMag
import IsingModel.TranslationInvariance

/-!
# ℤ^d `correlation² ≤ 1` and `-1 ≤ magnetization*` wrappers

Narrow child module for six ℤ^d wrappers extracted from
`UniformMagAbsBounds.lean`: `correlation{Λ,AlongExhaustion,Infinite}_sq_le_one`
and `neg_one_le_magnetization{Λ,AlongExhaustion,Infinite}`. Each wrapper is a
thin pass-through to the corresponding ambient lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `correlationΛ² ≤ 1`**. -/
theorem correlationΛ_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ (IsingModel.latticeGraph d) Λ p A ^ 2 ≤ 1 :=
  correlationΛ_sq_le_one (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `correlationAlongExhaustion² ≤ 1`** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n ^ 2 ≤ 1 :=
  correlationAlongExhaustion_sq_le_one (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d `correlationInfinite² ≤ 1`**. -/
theorem correlationInfinite_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p A ^ 2 ≤ 1 :=
  correlationInfinite_sq_le_one (IsingModel.latticeGraph d) Λ p A

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
