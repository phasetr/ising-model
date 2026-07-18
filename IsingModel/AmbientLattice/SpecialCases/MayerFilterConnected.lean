import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaCapstones

/-!
# Mayer filter-connected wrappers along an exhaustion

Narrow child module for the §18.5 Mayer filter-connected and epsilon-power
wrappers along an exhaustion. The theorem names are the same as the former
declarations, but callers can now avoid importing the monolithic
special-cases original module.

The two `mayerExpansionTermAlongExhaustion_filter_connected_{zero,one}`
base-case wrappers (previously in `MayerFilterConnectedBase.lean`) are
merged here as of the #4563 cycle-14 fixed-cost consolidation. Each such
wrapper is a thin pass-through to the corresponding ambient
`mayerExpansionTerm_Λ_filter_connected_{zero,one}` lemma stating that the
filter-connected piFinset is empty at `k = 0` and the entire piFinset at
`k = 1`. All theorem names/statements are preserved verbatim.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 Mayer filter-connected base cases -/

/-- **Along-ex: mayerExpansionTerm filter-connected at k=0 = ∅**. -/
theorem mayerExpansionTermAlongExhaustion_filter_connected_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    (Fintype.piFinset
        (fun _ : Fin 0 =>
          IsingModel.allPolymers
            (inducedGraph G (Λ.volume n)))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) = ∅ :=
  mayerExpansionTerm_Λ_filter_connected_zero G (Λ.volume n) t

/-- **Along-ex: mayerExpansionTerm filter-connected at k=1 = full
piFinset**. -/
theorem mayerExpansionTermAlongExhaustion_filter_connected_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    (Fintype.piFinset
        (fun _ : Fin 1 =>
          IsingModel.allPolymers
            (inducedGraph G (Λ.volume n)))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) =
      Fintype.piFinset
        (fun _ : Fin 1 =>
          IsingModel.allPolymers
            (inducedGraph G (Λ.volume n))) :=
  mayerExpansionTerm_Λ_filter_connected_one G (Λ.volume n)

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
