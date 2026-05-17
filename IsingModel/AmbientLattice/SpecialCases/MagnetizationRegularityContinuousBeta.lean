import IsingModel.AmbientLattice.Defs
import IsingModel.AmbientLattice.Exhaustion

/-!
# Magnetization `Continuous` in `β` along-ex wrapper

Narrow child module for the along-exhaustion
`magnetizationAlongExhaustion_continuous_beta` wrapper extracted
from `MagnetizationRegularity.lean`. The wrapper unfolds
`magnetizationAlongExhaustion` and dispatches on
`{i} ⊆ Λ.volume n`, falling back to the constant-zero function
off-volume and forwarding to `magnetizationΛ_continuous_beta`
on-volume. The theorem name is unchanged from the former
`MagnetizationRegularity` declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: magnetization Continuous in `β`** (general h). -/
theorem magnetizationAlongExhaustion_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : V) (n : ℕ) :
    Continuous (fun β' =>
      magnetizationAlongExhaustion G Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact magnetizationΛ_continuous_beta G (Λ.volume n) J h _
  · simp only [hi, dif_neg, not_false_iff]
    exact continuous_const

end Ambient
end IsingModel
