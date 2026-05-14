import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient freeEnergyAlongExhaustion continuity / differentiability wrappers

Narrow child module for 8 ambient `freeEnergyAlongExhaustion_*`
`Continuous` / `Differentiable` regularity wrappers extracted from
`PartitionFreeEnergyRegularity.lean`:

* `freeEnergyAlongExhaustion_{continuous,differentiable}_joint`,
* `freeEnergyAlongExhaustion_{continuous,differentiable}_beta`,
* `freeEnergyAlongExhaustion_{continuous,differentiable}_field`,
* `freeEnergyAlongExhaustion_{continuous,differentiable}_J`.

Each result is a thin pass-through of the corresponding Λ-level
`freeEnergyΛ_{continuous,differentiable}_*` lemma. The theorem names
are unchanged from the former `PartitionFreeEnergyRegularity`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


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
