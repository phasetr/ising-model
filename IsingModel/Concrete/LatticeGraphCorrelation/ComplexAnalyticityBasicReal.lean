import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d real analyticity of the partition function and of the free-energy density

Instantiates on a fixed finite volume `Λ : Finset (Fin d → ℤ)` of `IsingModel.latticeGraph d`
the real analyticity of the partition function and of the free-energy density in the external
field and in the coupling, the remaining parameters being held fixed. The partition-function
statements are pointwise, at an arbitrary real base point of the differentiated variable; the
free-energy statements are set-level, and are asserted only on the open half-line `Set.Ioi 0`
of the differentiated variable. None of them carries a hypothesis.
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
