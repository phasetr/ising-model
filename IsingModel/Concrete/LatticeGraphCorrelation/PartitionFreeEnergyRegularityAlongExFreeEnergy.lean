import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularityFE

/-!
# Concrete along-ex freeEnergyAlongExhaustion regularity wrappers

Narrow child module for eight ℤ^d `freeEnergyAlongExhaustion_latticeGraph_*`
`Continuous` / `Differentiable` regularity wrappers (joint, β, field h,
J). Each wrapper is a thin pass-through to the corresponding ambient
`freeEnergyAlongExhaustion_*` lemma at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: freeEnergy jointly Continuous**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) :=
  Ambient.freeEnergyAlongExhaustion_continuous_joint
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: freeEnergy jointly Differentiable ℝ**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) :=
  Ambient.freeEnergyAlongExhaustion_differentiable_joint
    (IsingModel.latticeGraph d) Λ n

/-! ### ℤ^d along-ex freeEnergy per-parameter regularity -/

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` Continuous in β** (general h). -/
theorem freeEnergyAlongExhaustion_latticeGraph_continuous_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J, h, β'⟩ : IsingParams ℝ) n) :=
  Ambient.freeEnergyAlongExhaustion_continuous_beta
    (IsingModel.latticeGraph d) Λ J h n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` Differentiable in β** (general h). -/
theorem freeEnergyAlongExhaustion_latticeGraph_differentiable_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J, h, β'⟩ : IsingParams ℝ) n) :=
  Ambient.freeEnergyAlongExhaustion_differentiable_beta
    (IsingModel.latticeGraph d) Λ J h n

/-! ## Moved: field/J regularity wrappers

The four wrappers
`freeEnergyAlongExhaustion_latticeGraph_continuous_field`,
`freeEnergyAlongExhaustion_latticeGraph_differentiable_field`,
`freeEnergyAlongExhaustion_latticeGraph_continuous_J`,
`freeEnergyAlongExhaustion_latticeGraph_differentiable_J` now live in
`PartitionFreeEnergyRegularityAlongExFreeEnergyFieldJ.lean`. -/



end Ambient
end IsingModel
