import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete per-direction real analyticity wrappers

Narrow child module for 4 ℤ^d per-direction real analyticity wrappers
extracted from `ComplexAnalyticityBasic.lean`:

* `partitionFunctionH_analyticAt_latticeGraph`,
* `freeEnergyH_analyticOn_latticeGraph`,
* `partitionFunctionJ_analyticAt_latticeGraph`,
* `freeEnergyJ_analyticOn_latticeGraph`.

Each is a thin pass-through of the corresponding ambient
`IsingModel.{partitionFunction,freeEnergy}{H,J}_analytic{At,On}`
lemma at `Ambient.inducedGraph (IsingModel.latticeGraph d) Λ`. The
theorem names are unchanged from the former `ComplexAnalyticityBasic`
declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `partitionFunction` analytic in `h`** at Λ-induced subgraph. -/
theorem partitionFunctionH_analyticAt_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β h₀ : ℝ) :
    AnalyticAt ℝ
      (fun h => partitionFunctionΛ (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩) h₀ :=
  IsingModel.partitionFunctionH_analyticAt
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `freeEnergyH` analytic on `(0, ∞)`** at Λ-induced subgraph. -/
theorem freeEnergyH_analyticOn_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    AnalyticOn ℝ
      (IsingModel.freeEnergyH
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β)
      (Set.Ioi 0) :=
  IsingModel.freeEnergyH_analyticOn
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `partitionFunction` analytic in `J`** at Λ-induced subgraph. -/
theorem partitionFunctionJ_analyticAt_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β J₀ : ℝ) :
    AnalyticAt ℝ
      (fun J => partitionFunctionΛ (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩) J₀ :=
  IsingModel.partitionFunctionJ_analyticAt
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β J₀

/-- **ℤ^d `freeEnergyJ` analytic on `(0, ∞)`** at Λ-induced subgraph. -/
theorem freeEnergyJ_analyticOn_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) :
    AnalyticOn ℝ
      (IsingModel.freeEnergyJ
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β)
      (Set.Ioi 0) :=
  IsingModel.freeEnergyJ_analyticOn
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

end Ambient

end IsingModel
