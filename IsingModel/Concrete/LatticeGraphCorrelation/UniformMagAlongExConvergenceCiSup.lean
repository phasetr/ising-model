import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d infinite-volume observables as stagewise suprema

Identifies the ℤ^d infinite-volume correlation and single-site magnetization with the `⨆`
over the stages of an exhaustion, and records the pointwise bound of each stage by that
infinite-volume value. None of these statements constrains the parameters.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `magnetizationInfinite` as `ciSup`**:
`magnetizationInfinite = ⨆ n, magnetizationAlongExhaustion`. -/
theorem magnetizationInfinite_latticeGraph_eq_ciSup
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ p i
      = ⨆ n, magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n :=
  magnetizationInfinite_eq_ciSup (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `correlationInfinite` as `ciSup`**. -/
theorem correlationInfinite_latticeGraph_eq_ciSup
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p A
      = ⨆ n, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n :=
  correlationInfinite_eq_ciSup (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `correlationAlongExhaustion ≤ correlationInfinite`** pointwise. -/
theorem correlationAlongExhaustion_le_correlationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p A :=
  correlationAlongExhaustion_le_correlationInfinite (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d `magnetizationAlongExhaustion ≤ magnetizationInfinite`** pointwise. -/
theorem magnetizationAlongExhaustion_le_magnetizationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ p i :=
  magnetizationAlongExhaustion_le_magnetizationInfinite
    (IsingModel.latticeGraph d) Λ p i n

end Ambient
end IsingModel
