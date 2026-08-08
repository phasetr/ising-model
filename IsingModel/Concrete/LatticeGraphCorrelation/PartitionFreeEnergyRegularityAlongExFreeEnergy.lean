import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularityFE

/-!
# Concrete along-ex freeEnergyAlongExhaustion regularity wrappers

Instantiates continuity and differentiability of the along-exhaustion free energy at
`IsingModel.latticeGraph d`, jointly and in the `β` direction, the ℤ^d input for the
GJ §17.5–§17.6 derivative arguments.
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

end Ambient
end IsingModel
