import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening

/-!
# A strict-bound criterion at a `tanh` activity, in terms of the reduced sum

Stage-`n` statement for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. It takes `DecidableEq V` and
the stagewise `Fintype` instance on that subgraph's edge set, and has `0 ≤ β * J` as its only
Prop-valued hypothesis.

Write `ε(t)` for the sum of `∏ P ∈ Γ, t ^ P.card` over the vertex-disjoint compatible polymer
families `Γ` of the stage subgraph with the empty family erased from the index set.

Under `0 ≤ β * J`, the polymer free energy at the activity `Real.tanh (β * J)` is strictly
below `ε(Real.tanh (β * J))` if and only if that value `ε(Real.tanh (β * J))` is positive.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: pFE(tanh) < ε(tanh) ↔ 0 < ε(tanh)** under
`0 ≤ β·J`. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_lt_eps_iff_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_Λ_tanh_lt_eps_iff_eps_pos G (Λ.volume n) hβJ

end Ambient
end IsingModel
