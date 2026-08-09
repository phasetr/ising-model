import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Basic

/-!
# ℤ^d single-variable analyticity of the complex partition function

Instantiates at the subgraph induced on a fixed finite volume `Λ : Finset (Fin d → ℤ)` of
`IsingModel.latticeGraph d` the analyticity of the complex partition function separately in
the external field, in the coupling and in the inverse temperature, the other two parameters
being held fixed. Each statement holds at an arbitrary base point of the
differentiated variable and carries no hypothesis at all.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `partitionFunctionComplex` entire in `h`** (Λ-induced). -/
theorem partitionFunctionComplex_analyticAt_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β h₀ : ℂ) :
    AnalyticAt ℂ (fun h => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) h₀ :=
  IsingModel.partitionFunctionComplex_analyticAt_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `partitionFunctionComplex` entire in `J`** (Λ-induced). -/
theorem partitionFunctionComplex_analyticAt_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β J₀ : ℂ) :
    AnalyticAt ℂ (fun J => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) J₀ :=
  IsingModel.partitionFunctionComplex_analyticAt_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β J₀

/-- **ℤ^d `partitionFunctionComplex` entire in `β`** (Λ-induced). -/
theorem partitionFunctionComplex_analyticAt_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β₀ : ℂ) :
    AnalyticAt ℂ (fun β => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) β₀ :=
  IsingModel.partitionFunctionComplex_analyticAt_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β₀

end Ambient
end IsingModel
