import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularity

/-!
# Concrete partition/free-energy pointwise regularity wrappers

This module contains concrete `latticeGraph` specializations of ambient
`ContinuousAt` and `DifferentiableAt` APIs for along-exhaustion partition
function and free energy. It is split out of the legacy concrete correlation
module so downstream users can depend on a narrower child path.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d along-ex `partitionFunctionAlongExhaustion` /
`freeEnergyAlongExhaustion` pointwise wrappers -/

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` ContinuousAt β at h = 0**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_continuousAt_beta_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    ContinuousAt (fun β' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, 0, β'⟩ n) β :=
  Ambient.partitionFunctionAlongExhaustion_continuousAt_beta_h_zero
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` ContinuousAt J at h = 0**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_continuousAt_J_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    ContinuousAt (fun J' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', 0, β⟩ n) J :=
  Ambient.partitionFunctionAlongExhaustion_continuousAt_J_h_zero
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` DifferentiableAt β at h = 0**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_differentiableAt_beta_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun β' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, 0, β'⟩ n) β :=
  Ambient.partitionFunctionAlongExhaustion_differentiableAt_beta_h_zero
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` DifferentiableAt J at h = 0**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_differentiableAt_J_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun J' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', 0, β⟩ n) J :=
  Ambient.partitionFunctionAlongExhaustion_differentiableAt_J_h_zero
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` ContinuousAt β at general h**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_continuousAt_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun β' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, h, β'⟩ n) β :=
  Ambient.partitionFunctionAlongExhaustion_continuousAt_beta_general_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` ContinuousAt J at general h**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_continuousAt_J_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun J' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', h, β⟩ n) J :=
  Ambient.partitionFunctionAlongExhaustion_continuousAt_J_general_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` DifferentiableAt β at general h**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_differentiableAt_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun β' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, h, β'⟩ n) β :=
  Ambient.partitionFunctionAlongExhaustion_differentiableAt_beta_general_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` DifferentiableAt J at general h**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_differentiableAt_J_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun J' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', h, β⟩ n) J :=
  Ambient.partitionFunctionAlongExhaustion_differentiableAt_J_general_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` ContinuousAt h**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_continuousAt_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun h' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, h', β⟩ n) h :=
  Ambient.partitionFunctionAlongExhaustion_continuousAt_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` DifferentiableAt h**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_differentiableAt_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun h' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, h', β⟩ n) h :=
  Ambient.partitionFunctionAlongExhaustion_differentiableAt_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` jointly ContinuousAt**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_continuousAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨q.2.1, q.2.2, q.1⟩ n) p :=
  Ambient.partitionFunctionAlongExhaustion_continuousAt_joint
    (IsingModel.latticeGraph d) Λ n p

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` jointly DifferentiableAt**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_differentiableAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨q.2.1, q.2.2, q.1⟩ n) p :=
  Ambient.partitionFunctionAlongExhaustion_differentiableAt_joint
    (IsingModel.latticeGraph d) Λ n p

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

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` ContinuousAt J**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_continuousAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun J' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', h, β⟩ n) J :=
  Ambient.freeEnergyAlongExhaustion_continuousAt_J
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` DifferentiableAt J**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_differentiableAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun J' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', h, β⟩ n) J :=
  Ambient.freeEnergyAlongExhaustion_differentiableAt_J
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` jointly ContinuousAt**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_continuousAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨q.2.1, q.2.2, q.1⟩ n) p :=
  Ambient.freeEnergyAlongExhaustion_continuousAt_joint
    (IsingModel.latticeGraph d) Λ n p

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` jointly DifferentiableAt**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_differentiableAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨q.2.1, q.2.2, q.1⟩ n) p :=
  Ambient.freeEnergyAlongExhaustion_differentiableAt_joint
    (IsingModel.latticeGraph d) Λ n p

end Ambient
end IsingModel
