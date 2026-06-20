import IsingModel.ClusterExpansion.RootedParentActiveLeafPeelInduction
import IsingModel.ClusterExpansion.Penrose.CompleteGraphTreeBound

/-!
# Relaxing the tree child-count factorial sum to all parent functions (GJ §18.5)

The convergent cluster-expansion closing needs a summable bound on
`∑_{T : ST(K_{n+1})} ∏_v (childCount T v)!`, where `childCount T v` is the number of
children of `v` in the rooted spanning tree `T`.  Because the complete-graph
spanning-tree parent code `completeGraphTreeParentCode` injects spanning trees into
parent functions `Fin n → Fin (n + 1)` (`completeGraphTreeParentCode_injective`), and the
child count is exactly the parent-function fiber size, the tree sum is dominated by the
sum over *all* parent functions:

`∑_{T} ∏_v (childCount T v)! ≤ ∑_{p : Fin n → Fin (n+1)} ∏_v (fiber count of p at v)!`.

This relaxation (Prüfer-free) isolates the combinatorial evaluation of the parent-function
sum (which equals `(2n)!/n! = n!·\binom{2n}{n} ≤ 4^n·n!`) from the tree-specific
machinery.

* `sum_completeGraphTrees_prod_childCount_factorial_le`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion / tree-graph inequality).
-/

namespace IsingModel

open Finset

variable {n : ℕ}

/-- **The tree child-count factorial sum is dominated by the parent-function sum.**
Summing the product of child-count factorials over the complete-graph spanning-tree
shapes is at most the same sum over all parent functions `Fin n → Fin (n + 1)`, since the
parent code injects spanning trees into parent functions and the child count
`rootedParentChildCount (completeGraphTreeParentCode n T) univ` is exactly the
parent-function fiber size.  The product is over natural-number factorials, so the
relaxation is monotone. -/
theorem sum_completeGraphTrees_prod_childCount_factorial_le :
    (∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
        S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
        ∏ v : Fin (n + 1),
          (rootedParentChildCount (Penrose.completeGraphTreeParentCode n T)
            (Finset.univ : Finset (Fin n)) v).factorial)
      ≤ ∑ p : Fin n → Fin (n + 1),
          ∏ v : Fin (n + 1),
            (rootedParentChildCount p (Finset.univ : Finset (Fin n)) v).factorial := by
  classical
  set g : (Fin n → Fin (n + 1)) → ℕ := fun p =>
    ∏ v : Fin (n + 1),
      (rootedParentChildCount p (Finset.univ : Finset (Fin n)) v).factorial with hg
  have hsum_tree :
      (∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
          S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          g (Penrose.completeGraphTreeParentCode n T))
        = ∑ p ∈ Finset.univ.image (Penrose.completeGraphTreeParentCode n), g p := by
    rw [Finset.sum_image fun T₁ _ T₂ _ h =>
      Penrose.completeGraphTreeParentCode_injective n h]
  rw [hsum_tree]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end IsingModel
