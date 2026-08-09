import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaCapstones

/-!
# Connected polymer sequences at small order, and powers of the reduced family sum

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Inside the length-`k` sequences of the stage subgraph's polymers sits the sub-finset on
which the incompatibility graph of the sequence is connected. That sub-finset is empty at
`k = 0`; it is the whole finset at `k = 1`; and at `k = 2` it is the sub-finset on which the
entry at index `0` and the entry at index `1` are incompatible.

Write `ε(t)` for the sum of `∏ P ∈ Γ, t ^ P.card` over the vertex-disjoint compatible
polymer families of the stage subgraph other than the empty family. Its `k`-th power is
expanded as the sum, over length-`k` sequences `ω` of such families, of
`∏ i, ∏ P ∈ ω i, t ^ P.card`.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

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
