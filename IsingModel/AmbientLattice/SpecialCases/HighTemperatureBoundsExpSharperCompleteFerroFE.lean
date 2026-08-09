import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperCompleteFE

/-!
# The packaged zero-field free-energy summary under `0 ≤ J` and `0 < β`

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume.

Under `0 ≤ J`, `0 < β` and a nonempty stage volume, a conjunction records the two-sided
bound `Real.log 2 + (|E| / |Λ|) * Real.log (Real.cosh (β * J)) ≤ f` and
`f ≤ Real.log 2 + β * J * |E| / |Λ|` at the parameter record `⟨J, 0, β⟩`, together with the
values `f = Real.log 2` at `⟨0, 0, β⟩` and at `⟨J, 0, 0⟩`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic f complete-summary exp bundle at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : (Λ.volume n).Nonempty) :
    Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2 +
          β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card ∧
    freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n = Real.log 2 ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n = Real.log 2 :=
  freeEnergyAlongExhaustion_high_temp_h_zero_complete_summary_exp
    G Λ J β (mul_nonneg hβ.le hJ) n hne

end Ambient

end IsingModel
