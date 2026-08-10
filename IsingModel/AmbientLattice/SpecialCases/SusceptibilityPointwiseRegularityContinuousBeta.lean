import IsingModel.AmbientLattice.MagnetizationAlongExhaustion

/-!
# Continuity of the stage susceptibility in the inverse temperature

Stage-`n` statement for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. It takes `DecidableEq V` and
the stagewise `Fintype` instance on that subgraph's edge set, and carries no Prop-valued
hypothesis.

At a site `i : V` and arbitrary `J` and `h`, the stage susceptibility is continuous on `ℝ` as
a function of the inverse temperature. The site is arbitrary: the proof splits on
`i ∈ Λ.volume n`, applying the finite-volume continuity on one branch and reading the stage
susceptibility as a constant on the other.
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
