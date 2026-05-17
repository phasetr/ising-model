import IsingModel.AmbientLattice.Defs
import IsingModel.AmbientLattice.Exhaustion

/-!
# Magnetization `Differentiable` in `β` along-ex wrapper

Narrow child module for the along-exhaustion
`magnetizationAlongExhaustion_differentiable_beta` wrapper extracted
from `MagnetizationRegularityDifferentiable.lean`. The wrapper
unfolds `magnetizationAlongExhaustion` and dispatches on whether
`{i} ⊆ Λ.volume n`, falling back to the constant-zero function
off-volume and to `magnetizationΛ_differentiable_beta` on-volume.
The theorem name is unchanged from the former
`MagnetizationRegularity` declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: magnetization Differentiable in `β`** (general h). -/
theorem magnetizationAlongExhaustion_differentiable_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ (fun β' =>
      magnetizationAlongExhaustion G Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact magnetizationΛ_differentiable_beta G (Λ.volume n) J h _
  · simp only [hi, dif_neg, not_false_iff]
    exact differentiable_const _

end Ambient
end IsingModel
