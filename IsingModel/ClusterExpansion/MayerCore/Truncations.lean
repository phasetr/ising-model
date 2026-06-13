import IsingModel.ClusterExpansion.MayerCore.PolymerBounds

/-!
# Mayer expansion truncation structure (GJ §18.4)

Structural results for the Mayer-expansion partial sums and the explicit
low-order Mayer terms, building on `mayerExpansionTerm` / `mayerPartialSum`
(`Terms.lean`) and the truncation recurrence `mayerPartialSum_succ`
(`PolymerBounds.lean`).  These advance the §18.4 Mayer expansion
`log Ξ = ∑_{n ≥ 0} mayerExpansionTerm G n t` (the general-`t` capstone is
the Mayer–Montroll exponential formula, deferred) by isolating the
explicit `n = 3` term as a triple sum and the `N = 3` partial sum.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4 (Mayer expansion), pp. 378–386.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Mayer expansion `n = 3` term as a triple sum**: reindexing the
`piFinset (Fin 3 → allPolymers G)` sum to a sum over ordered triples
`(P, Q, R) ∈ allPolymers G³`, the `n = 3` Mayer term is
`∑_{(P,Q,R)} ϕ^T(![P,Q,R]) · (t^|P|·t^|Q|·t^|R|)`.  The bijection
`ω ↦ (ω 0, ω 1, ω 2)` mirrors `mayerExpansionTerm_two`; the activity factor
`clusterSeqActivity t ω = ∏ᵢ t^|ω i|` collapses by `Fin.prod_univ_three`.
The Ursell coefficient `ϕ^T(![P,Q,R])` is left unevaluated (its closed form
for `n = 3` requires the connected-spanning classification of the
3-vertex incompatibility graph). -/
theorem mayerExpansionTerm_three
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerExpansionTerm G 3 t =
      ∑ pqr ∈ (allPolymers G) ×ˢ ((allPolymers G) ×ˢ (allPolymers G)),
        ursellCoefficient ![pqr.1, pqr.2.1, pqr.2.2] *
          (t ^ pqr.1.card * t ^ pqr.2.1.card * t ^ pqr.2.2.card) := by
  unfold mayerExpansionTerm
  apply Finset.sum_bij
    (fun (ω : Fin 3 → Finset (Sym2 ι)) (_ : ω ∈ _) => (ω 0, ω 1, ω 2))
  · intro ω hω
    rw [Fintype.mem_piFinset] at hω
    rw [Finset.mem_product, Finset.mem_product]
    exact ⟨hω 0, hω 1, hω 2⟩
  · intro ω₁ _ ω₂ _ heq
    funext i
    fin_cases i
    · exact (Prod.mk.inj heq).1
    · exact (Prod.mk.inj (Prod.mk.inj heq).2).1
    · exact (Prod.mk.inj (Prod.mk.inj heq).2).2
  · intro pqr hpqr
    rw [Finset.mem_product, Finset.mem_product] at hpqr
    refine ⟨![pqr.1, pqr.2.1, pqr.2.2], ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      fin_cases i
      · simpa using hpqr.1
      · simpa using hpqr.2.1
      · simpa using hpqr.2.2
    · rfl
  · intro ω hω
    have hω3 : ω = ![ω 0, ω 1, ω 2] := by
      funext i; fin_cases i <;> rfl
    rw [clusterSeqActivity, Fin.prod_univ_three]
    rw [← hω3]

/-- **Mayer partial sum at `N = 3`**: the truncation through cluster size
`3` adds the `n = 3` triple sum to the `N = 2` partial sum. -/
theorem mayerPartialSum_three
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerPartialSum G 3 t =
      mayerPartialSum G 2 t
        + ∑ pqr ∈ (allPolymers G) ×ˢ ((allPolymers G) ×ˢ (allPolymers G)),
            ursellCoefficient ![pqr.1, pqr.2.1, pqr.2.2] *
              (t ^ pqr.1.card * t ^ pqr.2.1.card * t ^ pqr.2.2.card) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, mayerPartialSum_succ, mayerExpansionTerm_three]

/-- **Mayer term vanishes when there are no polymers** (for `n ≥ 1`): if
`allPolymers G = ∅` then `mayerExpansionTerm G n t = 0` for every `n ≥ 1`,
since the `piFinset (Fin n → allPolymers G)` is empty (each coordinate must
land in the empty polymer set). -/
theorem mayerExpansionTerm_eq_zero_of_no_polymers
    (G : SimpleGraph ι) [Fintype G.edgeSet] (h_no : allPolymers G = ∅)
    {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    mayerExpansionTerm G n t = 0 := by
  unfold mayerExpansionTerm
  refine Finset.sum_eq_zero (fun ω hω => ?_)
  rw [Fintype.mem_piFinset] at hω
  have h0 : ω ⟨0, hn⟩ ∈ allPolymers G := hω _
  rw [h_no] at h0
  exact absurd h0 (Finset.notMem_empty _)

end IsingModel
