import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Basic

/-!
# ℤ^d single-variable analyticity of the complex free energy

Instantiates at the subgraph induced on a fixed finite volume `Λ : Finset (Fin d → ℤ)` of
`IsingModel.latticeGraph d` the analyticity of the complex free-energy density separately in
the external field, in the coupling and in the inverse temperature, the other two parameters
being held fixed. Each statement is conditional on `partitionFunctionComplex` lying in
`Complex.slitPlane` at the base point of the differentiated variable, and carries no further
hypothesis.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `freeEnergyComplex` analytic in `h`** (Λ-induced), on
`{Z ∈ slitPlane}`. -/
theorem freeEnergyComplex_analyticAt_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β h₀ : ℂ)
    (hZ : IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h₀ β
          ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) h₀ :=
  IsingModel.freeEnergyComplex_analyticAt_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀ hZ

/-- **ℤ^d `freeEnergyComplex` analytic in `J`** (Λ-induced), on
`{Z ∈ slitPlane}`. -/
theorem freeEnergyComplex_analyticAt_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β J₀ : ℂ)
    (hZ : IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J₀ h β
          ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun J => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) J₀ :=
  IsingModel.freeEnergyComplex_analyticAt_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β J₀ hZ

/-- **ℤ^d `freeEnergyComplex` analytic in `β`** (Λ-induced), on
`{Z ∈ slitPlane}`. -/
theorem freeEnergyComplex_analyticAt_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β₀ : ℂ)
    (hZ : IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β₀
          ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun β => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) β₀ :=
  IsingModel.freeEnergyComplex_analyticAt_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β₀ hZ

end Ambient
end IsingModel
