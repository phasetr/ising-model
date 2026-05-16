import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerFilterConnectedBase

/-!
# Mayer filter-connected wrappers along an exhaustion

Narrow child module for the §18.5 Mayer filter-connected and epsilon-power
wrappers along an exhaustion. The theorem names are the same as the former
former declarations, but callers can now avoid importing the monolithic
special-cases original module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 Mayer filter-connected + ε^n along-ex wraps -/

/-- **Along-ex: ε(t)^n as multi-Γ piFinset sum**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_pow
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (k : ℕ) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) ^ k =
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin k =>
                (IsingModel.vdCompatiblePolymerFamilies
                  (inducedGraph G (Λ.volume n))).erase ∅),
        ∏ i : Fin k, ∏ P ∈ ω i, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_minus_one_pow G (Λ.volume n) t k

/-! ## Moved: 2 filter_connected base-case wrappers

The two `mayerExpansionTermAlongExhaustion_filter_connected_{zero,one}`
base-case wrappers now live in
`IsingModel.AmbientLattice.SpecialCases.MayerFilterConnectedBase`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

/-- **Along-ex: filter-connected = filter-incompatible at k=2**. -/
theorem mayerExpansionTermAlongExhaustion_two_filter_connected_eq_incompat
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    (Fintype.piFinset
        (fun _ : Fin 2 =>
          IsingModel.allPolymers
            (inducedGraph G (Λ.volume n)))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) =
      (Fintype.piFinset
          (fun _ : Fin 2 =>
            IsingModel.allPolymers
              (inducedGraph G (Λ.volume n)))).filter
          (fun ω => IsingModel.PolymersIncompatible (ω 0) (ω 1)) :=
  mayerExpansionTerm_Λ_two_filter_connected_eq_incompat G (Λ.volume n)

end Ambient
end IsingModel
