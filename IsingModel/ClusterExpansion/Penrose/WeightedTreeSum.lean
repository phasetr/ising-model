import IsingModel.ClusterExpansion.Penrose.CompleteGraphTreeBound

/-!
# Weighted spanning-tree sum domination via the parent code (GJ §18.5)

The Kotecky--Preiss / tree-graph proof of cluster-expansion convergence (FV
Theorem 5.4) bounds a sum over spanning trees of the polymer incompatibility graph
by a product of per-vertex Kotecky--Preiss sums.  The combinatorial heart of that
step is a *weighted* version of the parent-code spanning-tree count bound
`numSpanningTrees (⊤ : SimpleGraph (Fin (n+1))) ≤ (n+1)^n`
(`CompleteGraphTreeBound`, i.e. `numSpanningTrees (⊤ Fin n) ≤ n^(n-1)`; this is the
parent-function relaxation, weaker than Cayley's exact `(n+1)^(n-1)`): the rooted
parent code
`completeGraphTreeParentCode` injects spanning trees of the complete graph into
parent functions `Fin n → Fin (n+1)`, so any non-negative weight summed over
spanning trees is dominated by the same weight summed over *all* parent functions.

* `completeGraphTreeParentCode_sum_le_sum_all_parentCodes`: for any non-negative
  `F`, `∑_{T spanning tree} F (parentCode T) ≤ ∑_{p : Fin n → Fin (n+1)} F p`,
  by `Finset.sum_image` with the existing injectivity of the parent code.
* `completeGraphTreeParentCode_weighted_sum_le_prod_parentSums`: specialising to a
  product weight `F p = ∏ i, c i (p i)` and factorising the unconstrained parent
  sum over independent vertex choices (`Finset.prod_sum`),
  `∑_{T} ∏_i c i (parentCode T i) ≤ ∏_i ∑_p c i p`.

This converts a sum over the *constrained* set of spanning trees into a product of
*independent* per-vertex sums — the latter being exactly the per-vertex
Kotecky--Preiss activity sums.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion / tree-graph inequality).
-/

namespace IsingModel.Penrose

open Finset

/-- **Parent-code domination of a weighted spanning-tree sum.**  For any
non-negative weight `F` on parent functions, the sum over spanning trees of the
complete graph `K_{n+1}` of `F (parentCode T)` is at most the sum of `F` over *all*
parent functions `Fin n → Fin (n+1)`.  The rooted parent code injects spanning
trees into parent functions (`completeGraphTreeParentCode_injective`), so the
spanning-tree sum is a sub-sum of the full parent-function sum. -/
theorem completeGraphTreeParentCode_sum_le_sum_all_parentCodes
    (n : ℕ) (F : (Fin n → Fin (n + 1)) → ℝ) (hF : ∀ p, 0 ≤ F p) :
    (∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
        S ∈ spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
        F (completeGraphTreeParentCode n T))
      ≤ ∑ p : Fin n → Fin (n + 1), F p := by
  have himg : (∑ p ∈ Finset.univ.image (completeGraphTreeParentCode n), F p)
      = ∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
          S ∈ spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          F (completeGraphTreeParentCode n T) :=
    Finset.sum_image fun x _ y _ h => completeGraphTreeParentCode_injective n h
  rw [← himg]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ => hF p

/-- **Weighted spanning-tree sum bounded by a product of per-vertex sums.**  For a
non-negative edge weight `c i p` (vertex `Fin.succ i` joined to parent `p`), the sum
over spanning trees of `K_{n+1}` of the parent-edge product is at most the product
over vertices of the unconstrained parent sums:
`∑_{T} ∏_i c i (parentCode T i) ≤ ∏_i ∑_p c i p`.  This is the key factorisation
turning a constrained spanning-tree sum into independent per-vertex sums. -/
theorem completeGraphTreeParentCode_weighted_sum_le_prod_parentSums
    (n : ℕ) (c : Fin n → Fin (n + 1) → ℝ) (hc : ∀ i p, 0 ≤ c i p) :
    (∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
        S ∈ spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
        ∏ i : Fin n, c i (completeGraphTreeParentCode n T i))
      ≤ ∏ i : Fin n, ∑ p : Fin (n + 1), c i p := by
  have hfact : (∑ p : Fin n → Fin (n + 1), ∏ i, c i (p i))
      = ∏ i : Fin n, ∑ p : Fin (n + 1), c i p := (Fintype.prod_sum c).symm
  exact (completeGraphTreeParentCode_sum_le_sum_all_parentCodes n
    (fun p => ∏ i, c i (p i)) fun p => Finset.prod_nonneg fun i _ => hc i (p i)).trans_eq hfact

end IsingModel.Penrose
