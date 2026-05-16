import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerRecurrenceHasSumLog

/-!
# Mayer recurrence and polymer free-energy HasSum wrappers along an exhaustion

Narrow child module for along-exhaustion Mayer recurrence wrappers,
`polymerFreeEnergy` log-series `HasSum` wrappers, and the
`vdPolymerFamilies_sum - 1` tendsto-zero wrapper. This keeps callers that only
need these forwarders out of the monolithic original special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 Mayer recurrence + hasSum + tendsto along-ex wraps -/

/-- **Along-ex: mayerPartialSum recurrence** in `N`. -/
theorem mayerPartialSumAlongExhaustion_succ
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n))
        (N + 1) t =
      IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n)) N t +
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) (N + 1) t :=
  mayerPartialSum_Λ_succ G (Λ.volume n) N t

/-- **Along-ex: mayerExpansionTerm = mayerPartialSum diff**. -/
theorem mayerExpansionTermAlongExhaustion_eq_mayerPartialSum_diff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) (N + 1) t =
      IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) (N + 1) t -
        IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n)) N t :=
  mayerExpansionTerm_Λ_eq_mayerPartialSum_diff G (Λ.volume n) N t

/-! ## Moved: 2 polymerFreeEnergy_hasSum_via_log wrappers

The two along-ex polymer free-energy log-series `HasSum` wrappers
(`polymerFreeEnergyAlongExhaustion_hasSum_via_log`,
`polymerFreeEnergyAlongExhaustion_hasSum_via_log_eventually`) now
live in
`IsingModel.AmbientLattice.SpecialCases.MayerRecurrenceHasSumLog`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex: ε(t) → 0 as t → 0**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_tendsto_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Filter.Tendsto (fun t : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) (nhds 0) (nhds 0) :=
  vdPolymerFamilies_sum_Λ_minus_one_tendsto_zero G (Λ.volume n)

end Ambient
end IsingModel
