import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularity

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

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` Continuous in h**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_continuous_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Continuous (fun h' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J, h', β⟩ : IsingParams ℝ) n) :=
  Ambient.freeEnergyAlongExhaustion_continuous_field
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` Differentiable in h**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_differentiable_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun h' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J, h', β⟩ : IsingParams ℝ) n) :=
  Ambient.freeEnergyAlongExhaustion_differentiable_field
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` Continuous in J**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_continuous_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J', h, β⟩ : IsingParams ℝ) n) :=
  Ambient.freeEnergyAlongExhaustion_continuous_J
    (IsingModel.latticeGraph d) Λ h β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` Differentiable in J**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_differentiable_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J', h, β⟩ : IsingParams ℝ) n) :=
  Ambient.freeEnergyAlongExhaustion_differentiable_J
    (IsingModel.latticeGraph d) Λ h β n


end Ambient
end IsingModel
