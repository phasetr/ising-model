import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureCapstonesPartition

/-!
# High-temperature capstone wrappers along an exhaustion

Narrow child module for the §18.6 free-energy capstone wrappers
along an exhaustion: the two `freeEnergyAlongExhaustion =
log 2 + cosh-correction + polymer correction` decompositions
(general and ferromagnetic), the `freeEnergyAlongExhaustion = log 2`
identity at `β · J = 0`, and the `mayerPartialSum_one_at_one`
identity. Theorem names are the same as the former legacy
declarations, but callers can now avoid importing the monolithic
special-cases legacy module.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ### §18.4-§18.6 capstones along-ex wraps -/

/-! ## Moved: 2 partitionFunctionAlongExhaustion polymer/even-subgraph closed forms

The two §18.4 partition-function high-temperature expansion
closed-form wrappers
(`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_polymer_family`,
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_evenSubgraphs`)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureCapstonesPartition`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

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
