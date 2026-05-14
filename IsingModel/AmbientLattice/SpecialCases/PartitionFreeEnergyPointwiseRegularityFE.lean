import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient freeEnergyAlongExhaustion pointwise wrappers

Narrow child module for 8 ambient `freeEnergyAlongExhaustion_*`
ContinuousAt / DifferentiableAt pointwise wrappers extracted from
`PartitionFreeEnergyPointwiseRegularity.lean`:

* `freeEnergyAlongExhaustion_continuousAt_beta`,
* `freeEnergyAlongExhaustion_differentiableAt_beta`,
* `freeEnergyAlongExhaustion_continuousAt_field`,
* `freeEnergyAlongExhaustion_differentiableAt_field`,
* `freeEnergyAlongExhaustion_continuousAt_J`,
* `freeEnergyAlongExhaustion_differentiableAt_J`,
* `freeEnergyAlongExhaustion_continuousAt_joint`,
* `freeEnergyAlongExhaustion_differentiableAt_joint`.

Each result is a thin pass-through lifting the corresponding Λ-level
`freeEnergyΛ_{continuous,differentiable}_*` lemma to AlongExhaustion
via `.continuousAt` / `.differentiableAt`. The theorem names are
unchanged from the former `PartitionFreeEnergyPointwiseRegularity`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-! ### Along-exhaustion free-energy pointwise wrappers -/

/-- **freeEnergyAlongExhaustion ContinuousAt β** (general h). -/
theorem freeEnergyAlongExhaustion_continuousAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) β :=
  (freeEnergyΛ_continuous_beta G (Λ.volume n) J h).continuousAt

/-- **freeEnergyAlongExhaustion DifferentiableAt β** (general h). -/
theorem freeEnergyAlongExhaustion_differentiableAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) β :=
  (freeEnergyΛ_differentiable_beta G (Λ.volume n) J h).differentiableAt

/-- **freeEnergyAlongExhaustion ContinuousAt h**. -/
theorem freeEnergyAlongExhaustion_continuousAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) h :=
  (freeEnergyΛ_continuous_field G (Λ.volume n) J β).continuousAt

/-- **freeEnergyAlongExhaustion DifferentiableAt h**. -/
theorem freeEnergyAlongExhaustion_differentiableAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) h :=
  (freeEnergyΛ_differentiable_field G (Λ.volume n) J β).differentiableAt

/-- **freeEnergyAlongExhaustion ContinuousAt J**. -/
theorem freeEnergyAlongExhaustion_continuousAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) J :=
  (freeEnergyΛ_continuous_J G (Λ.volume n) h β).continuousAt

/-- **freeEnergyAlongExhaustion DifferentiableAt J**. -/
theorem freeEnergyAlongExhaustion_differentiableAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) J :=
  (freeEnergyΛ_differentiable_J G (Λ.volume n) h β).differentiableAt

/-- **freeEnergyAlongExhaustion jointly ContinuousAt**. -/
theorem freeEnergyAlongExhaustion_continuousAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ n) p :=
  (freeEnergyΛ_continuous_joint G (Λ.volume n)).continuousAt

/-- **freeEnergyAlongExhaustion jointly DifferentiableAt**. -/
theorem freeEnergyAlongExhaustion_differentiableAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ n) p :=
  (freeEnergyΛ_differentiable_joint G (Λ.volume n)).differentiableAt


end Ambient
end IsingModel
