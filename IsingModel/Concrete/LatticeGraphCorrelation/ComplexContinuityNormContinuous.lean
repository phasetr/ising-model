import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.DomainGeometry

/-!
# ℤ^d continuity of the complex partition function

Instantiates at the subgraph induced on a fixed finite volume `Λ : Finset (Fin d → ℤ)` of
`IsingModel.latticeGraph d` the continuity of the complex partition function separately in
the external field, in the coupling and in the inverse temperature with the other two held
fixed, and jointly as a function on `ℂ × ℂ × ℂ`. No statement here carries a hypothesis.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `Continuous` form of `partitionFunctionComplex` in `h`**
(Λ-induced). -/
theorem continuous_partitionFunctionComplex_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    Continuous (fun h => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) :=
  IsingModel.continuous_partitionFunctionComplex_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `Continuous` form of `partitionFunctionComplex` in `J`**
(Λ-induced). -/
theorem continuous_partitionFunctionComplex_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℂ) :
    Continuous (fun J => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) :=
  IsingModel.continuous_partitionFunctionComplex_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

/-- **ℤ^d `Continuous` form of `partitionFunctionComplex` in `β`**
(Λ-induced). -/
theorem continuous_partitionFunctionComplex_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℂ) :
    Continuous (fun β => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) :=
  IsingModel.continuous_partitionFunctionComplex_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h

/-- **ℤ^d joint continuity of `partitionFunctionComplex`** (Λ-induced):
`(J, h, β) : ℂ × ℂ × ℂ ↦ Z_ℂ` is continuous. -/
theorem continuous_partitionFunctionComplex_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    Continuous (fun z : ℂ × ℂ × ℂ =>
      IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2) :=
  IsingModel.continuous_partitionFunctionComplex_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

end Ambient
end IsingModel
