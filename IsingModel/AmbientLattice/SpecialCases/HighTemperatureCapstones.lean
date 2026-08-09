import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureCapstonesPartition
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureCapstonesFreeEnergy

/-!
# The zero-field free energy at vanishing coupling, and a polymer count

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Under `β * J = 0` and a nonempty stage volume, the free energy at the parameter record
`⟨J, 0, β⟩` is `Real.log 2`.

Separately, the Mayer partial sum of the stage subgraph truncated at order `1` and read at
activity `1` is the cardinality of that subgraph's polymer universe
`IsingModel.allPolymers`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: freeEnergy = log 2 at `β·J = 0`** under
`(Λ.volume n).Nonempty`. -/
theorem freeEnergyAlongExhaustion_eq_log_two_at_betaJ_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ ⟨J, 0, β⟩ n = Real.log 2 :=
  freeEnergyΛ_eq_log_two_at_betaJ_zero G (Λ.volume n) hβJ hne

/-- **Along-ex: mayerPartialSum at N=1, t=1**. -/
theorem mayerPartialSumAlongExhaustion_one_at_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n)) 1 1 =
      (IsingModel.allPolymers (inducedGraph G (Λ.volume n))).card :=
  mayerPartialSum_Λ_one_at_one G (Λ.volume n)

end Ambient
end IsingModel
