import IsingModel.AmbientLattice.MagnetizationAlongExhaustion

/-!
# Ambient susceptibility `Continuous` in `β` per-parameter wrapper

Narrow child module for the along-exhaustion
`susceptibilityAlongExhaustion_continuous_beta_gen` wrapper
extracted from `SusceptibilityPointwiseRegularity.lean`. The
wrapper unfolds `susceptibilityAlongExhaustion` and dispatches on
`i ∈ Λ.volume n`, falling back to `continuous_const` off-volume
and forwarding to `susceptibilityΛ_continuous_beta` on-volume. The
theorem name is unchanged from the former
`SusceptibilityPointwiseRegularity` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: susceptibility Continuous in `β`** (general G, general h). -/
theorem susceptibilityAlongExhaustion_continuous_beta_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : V) (n : ℕ) :
    Continuous (fun β' =>
      susceptibilityAlongExhaustion G Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact susceptibilityΛ_continuous_beta G (Λ.volume n) J h _
  · simp only [hi, dif_neg, not_false_iff]
    exact continuous_const

end Ambient
end IsingModel
