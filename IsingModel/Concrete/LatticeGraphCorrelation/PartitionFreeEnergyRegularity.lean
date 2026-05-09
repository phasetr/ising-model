import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularity

/-!
# Concrete partition/free-energy regularity wrappers

This module contains concrete `latticeGraph` specializations of `Continuous`
and `Differentiable` APIs for partition functions and free energies. It is
split out of the legacy concrete correlation module so downstream users can
depend on a narrower child path.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d partition/free-energy Continuous and Differentiable -/

/-- **ℤ^d Λ: partitionFunction Continuous in `β` at general `h`**. -/
theorem partitionFunctionΛ_latticeGraph_continuous_beta_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h : ℝ) :
    Continuous (fun β' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, h, β'⟩) :=
  Ambient.partitionFunctionΛ_continuous_beta_general_h
    (IsingModel.latticeGraph d) Λ J h

/-- **ℤ^d Λ: partitionFunction Continuous in `J` at general `h`**. -/
theorem partitionFunctionΛ_latticeGraph_continuous_J_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β h : ℝ) :
    Continuous (fun J' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J', h, β⟩) :=
  Ambient.partitionFunctionΛ_continuous_J_general_h
    (IsingModel.latticeGraph d) Λ β h

/-- **ℤ^d Λ: partitionFunction Differentiable in `β` at general `h`**. -/
theorem partitionFunctionΛ_latticeGraph_differentiable_beta_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h : ℝ) :
    Differentiable ℝ (fun β' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, h, β'⟩) :=
  Ambient.partitionFunctionΛ_differentiable_beta_general_h
    (IsingModel.latticeGraph d) Λ J h

/-- **ℤ^d Λ: partitionFunction Differentiable in `J` at general `h`**. -/
theorem partitionFunctionΛ_latticeGraph_differentiable_J_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β h : ℝ) :
    Differentiable ℝ (fun J' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J', h, β⟩) :=
  Ambient.partitionFunctionΛ_differentiable_J_general_h
    (IsingModel.latticeGraph d) Λ β h

/-- **ℤ^d Λ: partitionFunction Continuous in `h`**. -/
theorem partitionFunctionΛ_latticeGraph_continuous_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) :
    Continuous (fun h' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, h', β⟩) :=
  Ambient.partitionFunctionΛ_continuous_h
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d Λ: partitionFunction Differentiable in `h`**. -/
theorem partitionFunctionΛ_latticeGraph_differentiable_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) :
    Differentiable ℝ (fun h' : ℝ =>
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, h', β⟩) :=
  Ambient.partitionFunctionΛ_differentiable_h
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d Λ: freeEnergy jointly Continuous**. -/
theorem freeEnergyΛ_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩) :=
  Ambient.freeEnergyΛ_continuous_joint
    (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: freeEnergy jointly Differentiable ℝ**. -/
theorem freeEnergyΛ_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩) :=
  Ambient.freeEnergyΛ_differentiable_joint
    (IsingModel.latticeGraph d) Λ

/-- **ℤ^d along-ex: partitionFunction Continuous in `β` at general
`h`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_continuous_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J h : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J, h, β'⟩ n) :=
  Ambient.partitionFunctionAlongExhaustion_continuous_beta_general_h
    (IsingModel.latticeGraph d) Λ J h n

/-- **ℤ^d along-ex: partitionFunction Continuous in `J` at general
`h`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_continuous_J_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β h : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J', h, β⟩ n) :=
  Ambient.partitionFunctionAlongExhaustion_continuous_J_general_h
    (IsingModel.latticeGraph d) Λ β h n

/-- **ℤ^d along-ex: partitionFunction Differentiable in `β` at
general `h`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_differentiable_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J h : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J, h, β'⟩ n) :=
  Ambient.partitionFunctionAlongExhaustion_differentiable_beta_general_h
    (IsingModel.latticeGraph d) Λ J h n

/-- **ℤ^d along-ex: partitionFunction Differentiable in `J` at
general `h`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_differentiable_J_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β h : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J', h, β⟩ n) :=
  Ambient.partitionFunctionAlongExhaustion_differentiable_J_general_h
    (IsingModel.latticeGraph d) Λ β h n

/-- **ℤ^d along-ex: partitionFunction Continuous in `h`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_continuous_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (n : ℕ) :
    Continuous (fun h' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J, h', β⟩ n) :=
  Ambient.partitionFunctionAlongExhaustion_continuous_h
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: partitionFunction Differentiable in `h`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_differentiable_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun h' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J, h', β⟩ n) :=
  Ambient.partitionFunctionAlongExhaustion_differentiable_h
    (IsingModel.latticeGraph d) Λ J β n

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
