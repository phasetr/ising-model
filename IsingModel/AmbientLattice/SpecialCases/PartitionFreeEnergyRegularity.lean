import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient partition/free-energy regularity wrappers

This module contains general-graph `Continuous` and `Differentiable` APIs for
per-stage `partitionFunctionAlongExhaustion` and `freeEnergyAlongExhaustion`.
It is split out of the legacy ambient special-cases module so concrete
partition/free-energy wrappers can depend on a narrower child path.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### Along-exhaustion partition/free-energy Continuous and Differentiable -/

/-- **Along-ex: partitionFunction Continuous in `β` at general `h`**. -/
theorem partitionFunctionAlongExhaustion_continuous_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h, β'⟩ n) :=
  partitionFunctionΛ_continuous_beta_general_h G (Λ.volume n) J h

/-- **Along-ex: partitionFunction Continuous in `J` at general `h`**. -/
theorem partitionFunctionAlongExhaustion_continuous_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β h : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', h, β⟩ n) :=
  partitionFunctionΛ_continuous_J_general_h G (Λ.volume n) β h

/-- **Along-ex: partitionFunction Differentiable in `β` at general
`h`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h, β'⟩ n) :=
  partitionFunctionΛ_differentiable_beta_general_h G (Λ.volume n) J h

/-- **Along-ex: partitionFunction Differentiable in `J` at general
`h`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β h : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', h, β⟩ n) :=
  partitionFunctionΛ_differentiable_J_general_h G (Λ.volume n) β h

/-- **Along-ex: partitionFunction Continuous in `h`**. -/
theorem partitionFunctionAlongExhaustion_continuous_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Continuous (fun h' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h', β⟩ n) :=
  partitionFunctionΛ_continuous_h G (Λ.volume n) J β

/-- **Along-ex: partitionFunction Differentiable in `h`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun h' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h', β⟩ n) :=
  partitionFunctionΛ_differentiable_h G (Λ.volume n) J β

/-- **Along-ex: freeEnergy jointly Continuous**. -/
theorem freeEnergyAlongExhaustion_continuous_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ n) :=
  freeEnergyΛ_continuous_joint G (Λ.volume n)

/-- **Along-ex: freeEnergy jointly Differentiable ℝ**. -/
theorem freeEnergyAlongExhaustion_differentiable_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ n) :=
  freeEnergyΛ_differentiable_joint G (Λ.volume n)

/-- **Along-ex: freeEnergy Continuous in β** (general h). -/
theorem freeEnergyAlongExhaustion_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) :=
  freeEnergyΛ_continuous_beta G (Λ.volume n) J h

/-- **Along-ex: freeEnergy Differentiable in β** (general h). -/
theorem freeEnergyAlongExhaustion_differentiable_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) :=
  freeEnergyΛ_differentiable_beta G (Λ.volume n) J h

/-- **Along-ex: freeEnergy Continuous in h**. -/
theorem freeEnergyAlongExhaustion_continuous_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Continuous (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) :=
  freeEnergyΛ_continuous_field G (Λ.volume n) J β

/-- **Along-ex: freeEnergy Differentiable in h**. -/
theorem freeEnergyAlongExhaustion_differentiable_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) :=
  freeEnergyΛ_differentiable_field G (Λ.volume n) J β

/-- **Along-ex: freeEnergy Continuous in J**. -/
theorem freeEnergyAlongExhaustion_continuous_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) :=
  freeEnergyΛ_continuous_J G (Λ.volume n) h β

/-- **Along-ex: freeEnergy Differentiable in J**. -/
theorem freeEnergyAlongExhaustion_differentiable_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) :=
  freeEnergyΛ_differentiable_J G (Λ.volume n) h β

end Ambient
end IsingModel
