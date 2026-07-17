import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.RealAxis

/-!
# Concrete Complex restrict-real-axis wrappers

Narrow child module for four ℤ^d
`{freeEnergy,partitionFunction}Complex_restrict_*_latticeGraph`
real-axis restriction wrappers (`restrict_real_axis_eq` /
`restrict_joint_real_eq`). Each wrapper is a thin pass-through to the
corresponding ambient `*_restrict_*` lemma at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `f_ℂ` restriction to real axis equals `f_ℝ`** (Λ-induced). -/
theorem freeEnergyComplex_restrict_real_axis_eq_freeEnergy_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    (fun h : ℝ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) (h : ℂ) (β : ℂ))
      = fun h : ℝ => ((IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          ⟨J, h, β⟩ : ℝ) : ℂ) :=
  IsingModel.freeEnergyComplex_restrict_real_axis_eq_freeEnergy
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `Z_ℂ` restriction to real axis equals `↑Z_ℝ`** (Λ-induced). -/
theorem partitionFunctionComplex_restrict_real_axis_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    (fun h : ℝ => IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) (h : ℂ) (β : ℂ))
      = fun h : ℝ => ((IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          ⟨J, h, β⟩ : ℝ) : ℂ) :=
  IsingModel.partitionFunctionComplex_restrict_real_axis_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `Z_ℂ` restriction to `IsingParams ℝ`-image = `↑Z_ℝ`**
(Λ-induced). -/
theorem partitionFunctionComplex_restrict_joint_real_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    (fun p : IsingParams ℝ => IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ))
      = fun p : IsingParams ℝ => ((IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p : ℝ) : ℂ) :=
  IsingModel.partitionFunctionComplex_restrict_joint_real_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d `f_ℂ` restriction to `IsingParams ℝ`-image = `↑f_ℝ`**
(Λ-induced). -/
theorem freeEnergyComplex_restrict_joint_real_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    (fun p : IsingParams ℝ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ))
      = fun p : IsingParams ℝ => ((IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p : ℝ) : ℂ) :=
  IsingModel.freeEnergyComplex_restrict_joint_real_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)


end Ambient
end IsingModel
