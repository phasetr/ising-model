import IsingModel.ClusterExpansion.Penrose.ParentCodeFactorialSum
import IsingModel.ClusterExpansion.Penrose.FiberFactorialSum

/-!
# The tree child-count factorial sum is at most `4^n·n!` (GJ §18.5)

Composing the tree → parent-function relaxation
(`sum_completeGraphTrees_prod_childCount_factorial_le`, #4124) with the closed-form
evaluation of the parent-function fiber-factorial sum
(`parentFiberFactorialSum_succ_le_four_pow_mul_factorial`, #4125) bounds the sum of
child-count factorials over complete-graph spanning trees by `4^n·n!`:

`∑_{T : ST(K_{n+1})} ∏_v (childCount T v)! ≤ 4^n·n!`.

The bridge is that `rootedParentChildCount p univ` and `fiberCount n (n+1) p` are the same
function (both `#{i | p i = v}`).

* `sum_completeGraphTrees_prod_childCount_factorial_le_four_pow_mul_factorial`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {n : ℕ}

/-- **The tree child-count factorial sum is at most `4^n·n!`.**  Summing the product of
child-count factorials over the complete-graph spanning-tree shapes is at most `4^n·n!`,
by relaxing to all parent functions (#4124) and evaluating that sum as `(2n)!/n! ≤ 4^n·n!`
(#4125).  The child count `rootedParentChildCount p univ` is the parent-function fiber
size `fiberCount n (n+1) p`. -/
theorem sum_completeGraphTrees_prod_childCount_factorial_le_four_pow_mul_factorial :
    (∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
        S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
        ∏ v : Fin (n + 1),
          (rootedParentChildCount (Penrose.completeGraphTreeParentCode n T)
            (Finset.univ : Finset (Fin n)) v).factorial)
      ≤ 4 ^ n * n.factorial := by
  refine sum_completeGraphTrees_prod_childCount_factorial_le.trans ?_
  -- The parent-function sum is exactly `parentFiberFactorialSum n (n+1)`.
  have hbridge : (∑ p : Fin n → Fin (n + 1),
        ∏ v : Fin (n + 1), (rootedParentChildCount p (Finset.univ : Finset (Fin n)) v).factorial)
      = parentFiberFactorialSum n (n + 1) := rfl
  rw [hbridge]
  exact parentFiberFactorialSum_succ_le_four_pow_mul_factorial n

end IsingModel
