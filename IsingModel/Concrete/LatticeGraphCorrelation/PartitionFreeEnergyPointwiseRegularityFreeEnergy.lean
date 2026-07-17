import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityFENonJoint

/-!
# Concrete freeEnergyAlongExhaustion pointwise regularity wrappers

Narrow child module for eight ℤ^d
`freeEnergyAlongExhaustion_latticeGraph_{continuousAt,differentiableAt}_*`
pointwise regularity wrappers. Each wrapper is a thin pass-through to
the corresponding ambient `freeEnergyAlongExhaustion_*` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` ContinuousAt β** (general h). -/
theorem freeEnergyAlongExhaustion_latticeGraph_continuousAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun β' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, h, β'⟩ n) β :=
  Ambient.freeEnergyAlongExhaustion_continuousAt_beta
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` DifferentiableAt β** (general h). -/
theorem freeEnergyAlongExhaustion_latticeGraph_differentiableAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun β' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, h, β'⟩ n) β :=
  Ambient.freeEnergyAlongExhaustion_differentiableAt_beta
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` ContinuousAt h**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_continuousAt_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun h' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, h', β⟩ n) h :=
  Ambient.freeEnergyAlongExhaustion_continuousAt_field
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` DifferentiableAt h**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_differentiableAt_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun h' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, h', β⟩ n) h :=
  Ambient.freeEnergyAlongExhaustion_differentiableAt_field
    (IsingModel.latticeGraph d) Λ J h β n

/-! ## Moved: J / joint pointwise regularity wrappers

The four wrappers
`freeEnergyAlongExhaustion_latticeGraph_continuousAt_J`,
`freeEnergyAlongExhaustion_latticeGraph_differentiableAt_J`,
`freeEnergyAlongExhaustion_latticeGraph_continuousAt_joint`,
`freeEnergyAlongExhaustion_latticeGraph_differentiableAt_joint` now
live in `PartitionFreeEnergyPointwiseRegularityFreeEnergyJJoint.lean`. -/


end Ambient
end IsingModel
