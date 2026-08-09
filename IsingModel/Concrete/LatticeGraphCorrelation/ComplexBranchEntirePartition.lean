import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.RealAxis

/-!
# ℤ^d entirety of the complex partition function

Instantiates at the subgraph induced on a fixed finite volume `Λ : Finset (Fin d → ℤ)` of
`IsingModel.latticeGraph d` the statement that the complex partition function is entire, that
is complex differentiable on the whole space: separately in the external field, in the
coupling and in the inverse temperature with the other two held fixed, and jointly in
`(J, h, β)`. No statement here carries a hypothesis.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `Z_ℂ` entire in `h` (Differentiable ℂ)** (Λ-induced). -/
theorem partitionFunctionComplex_entire_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    Differentiable ℂ (fun h => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) :=
  IsingModel.partitionFunctionComplex_entire_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `Z_ℂ` entire in `J` (Differentiable ℂ)** (Λ-induced). -/
theorem partitionFunctionComplex_entire_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℂ) :
    Differentiable ℂ (fun J => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) :=
  IsingModel.partitionFunctionComplex_entire_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

/-- **ℤ^d `Z_ℂ` entire in `β` (Differentiable ℂ)** (Λ-induced). -/
theorem partitionFunctionComplex_entire_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℂ) :
    Differentiable ℂ (fun β => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) :=
  IsingModel.partitionFunctionComplex_entire_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h

/-- **ℤ^d `Z_ℂ` jointly entire on ℂ³ (Differentiable ℂ)**
(Λ-induced). -/
theorem partitionFunctionComplex_entire_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    Differentiable ℂ
      (fun z : ℂ × ℂ × ℂ => IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2) :=
  IsingModel.partitionFunctionComplex_entire_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

end Ambient
end IsingModel
