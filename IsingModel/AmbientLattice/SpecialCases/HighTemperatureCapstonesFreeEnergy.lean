import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaCapstones

/-!
# The zero-field free energy as `Real.log 2` plus cosh and polymer corrections

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume.

Under `0 ≤ β * J` and a nonempty stage volume, the free energy at the parameter record
`⟨J, 0, β⟩` is `Real.log 2 + (|E| / |Λ|) * Real.log (Real.cosh (β * J))` plus
`IsingModel.polymerFreeEnergy` of the stage subgraph at `Real.tanh (β * J)`, divided by
`|Λ|`. The same identity is stated under `0 ≤ J` together with `0 < β` in place of
`0 ≤ β * J`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: §18.6 freeEnergy decomposition** under `0 ≤ β·J` and
`(Λ.volume n).Nonempty`. -/
theorem freeEnergyAlongExhaustion_eq_polymerFreeEnergy
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ ⟨J, 0, β⟩ n =
      Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
            Fintype.card ↑(Λ.volume n : Finset V) *
          Real.log (Real.cosh (β * J)) +
        IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
          (Real.tanh (β * J)) /
            Fintype.card ↑(Λ.volume n : Finset V) :=
  freeEnergyΛ_eq_polymerFreeEnergy G (Λ.volume n) J β hβJ hne

/-- **Along-ex: §18.6 ferromagnetic freeEnergy decomposition**. -/
theorem freeEnergyAlongExhaustion_eq_polymerFreeEnergy_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ ⟨J, 0, β⟩ n =
      Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
            Fintype.card ↑(Λ.volume n : Finset V) *
          Real.log (Real.cosh (β * J)) +
        IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
          (Real.tanh (β * J)) /
            Fintype.card ↑(Λ.volume n : Finset V) :=
  freeEnergyΛ_eq_polymerFreeEnergy_ferromagnetic
    G (Λ.volume n) J β hJ hβ hne

end Ambient
end IsingModel
