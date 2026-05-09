import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Mayer expansion edge-case wrappers along an exhaustion

Narrow child module for along-exhaustion Mayer expansion `n = 2`, no-polymer,
edgeless, and absolute-bound wrappers. This keeps callers that only need these
forwarders out of the monolithic legacy special-cases module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 Mayer expansion edge-cases + n=2 + abs_le along-ex -/

/-- **Along-ex: mayerExpansionTerm at `n = 2`**. -/
theorem mayerExpansionTermAlongExhaustion_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) 2 t =
      ∑ pq ∈ (IsingModel.allPolymers
              (inducedGraph G (Λ.volume n))) ×ˢ
              (IsingModel.allPolymers (inducedGraph G (Λ.volume n))),
        (if IsingModel.PolymersIncompatible pq.1 pq.2 then (-1/2 : ℝ)
          else 0) *
          (t ^ pq.1.card * t ^ pq.2.card) :=
  mayerExpansionTerm_Λ_two G (Λ.volume n) t

/-- **Along-ex: mayerExpansionTerm at `n = 2`, filter form**. -/
theorem mayerExpansionTermAlongExhaustion_two_filter
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) 2 t =
      (-1/2 : ℝ) *
        ∑ pq ∈ ((IsingModel.allPolymers
                  (inducedGraph G (Λ.volume n))) ×ˢ
                (IsingModel.allPolymers
                  (inducedGraph G (Λ.volume n)))).filter
            (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
          (t ^ pq.1.card * t ^ pq.2.card) :=
  mayerExpansionTerm_Λ_two_filter G (Λ.volume n) t

/-- **Along-ex: mayerPartialSum at `N = 2`**. -/
theorem mayerPartialSumAlongExhaustion_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n)) 2 t =
      (∑ P ∈ IsingModel.allPolymers (inducedGraph G (Λ.volume n)),
            t ^ P.card) +
        (-1/2 : ℝ) *
          ∑ pq ∈ ((IsingModel.allPolymers
                    (inducedGraph G (Λ.volume n))) ×ˢ
                  (IsingModel.allPolymers
                    (inducedGraph G (Λ.volume n)))).filter
              (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
            (t ^ pq.1.card * t ^ pq.2.card) :=
  mayerPartialSum_Λ_two G (Λ.volume n) t

/-- **Along-ex: mayerPartialSum = 0 on no-polymer graphs**. -/
theorem mayerPartialSumAlongExhaustion_eq_zero_of_no_polymers
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_no : IsingModel.allPolymers (inducedGraph G (Λ.volume n)) = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n)) N t = 0 :=
  mayerPartialSum_Λ_eq_zero_of_no_polymers G (Λ.volume n) h_no t N

/-- **Along-ex: mayerPartialSum = 0 on edgeless graphs**. -/
theorem mayerPartialSumAlongExhaustion_eq_zero_of_edgeFinset_empty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_empty : (inducedGraph G (Λ.volume n)).edgeFinset = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G (Λ.volume n)) N t = 0 :=
  mayerPartialSum_Λ_eq_zero_of_edgeFinset_empty
    G (Λ.volume n) h_empty t N

/-- **Along-ex: mayerExpansionTerm absolute bound**. -/
theorem mayerExpansionTermAlongExhaustion_abs_le
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (t : ℝ) (n : ℕ) :
    |IsingModel.mayerExpansionTerm (inducedGraph G (Λ.volume n)) k t| ≤
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin k => IsingModel.allPolymers
                (inducedGraph G (Λ.volume n))),
        |IsingModel.ursellCoefficient ω| *
          |IsingModel.clusterSeqActivity t ω| :=
  mayerExpansionTerm_Λ_abs_le G (Λ.volume n) k t

end Ambient
end IsingModel
