import IsingModel.ClusterExpansion.MayerCore.MayerTreeSumActivity

/-!
# Inserting the Kotecky--Preiss `e`-weights into the Mayer tree-sum bound (GJ §18.5)

Continuing the rooted-tree assembly of `MayerTreeSumActivity`, this inserts the
Kotecky--Preiss weight `e^{|Q|}` on the non-root factors of the activity product and
splits off the root vertex `0`.  Since `1 ≤ e^{|Q|}` and `|t|^{|Q|} ≥ 0`, the bare
activity `∏_i |t|^{|ω i|}` is dominated by the rooted, `e`-weighted form
`|t|^{|ω 0|} · ∏_{i} e^{|ω (succ i)|}·|t|^{|ω (succ i)|}`.

`mayerExpansionTerm_succ_abs_le_treeSum_rootedExpActivity`:
`|mayerExpansionTerm G (n+1) t| ≤ ((n+1)!)⁻¹ · ∑_ω ∑_{T tree of incompat(ω)}
   |t|^{|ω 0|} · ∏_{i : Fin n} e^{|ω (succ i)|}·|t|^{|ω (succ i)|}`.

The non-root factors are now in exactly the per-edge Kotecky--Preiss weight form
`e^{|Q|}·|t|^{|Q|}` of `polymerSeqTree_childActivityWeight_le_parentCard`, ready for
the parent-edge reduction and the weighted spanning-tree factorisation.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion / tree-graph inequality).
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Inserting the Kotecky--Preiss `e`-weights into the Mayer tree-sum bound.**
Splitting off the root vertex `0` and inserting `e^{|ω (succ i)|} ≥ 1` on the
non-root factors,
`|mayerExpansionTerm G (n+1) t| ≤ ((n+1)!)⁻¹ · ∑_ω ∑_{T tree of incompat(ω)}
   |t|^{|ω 0|} · ∏_i e^{|ω (succ i)|}·|t|^{|ω (succ i)|}`.
The non-root factors are in the per-edge Kotecky--Preiss weight form, ready for the
parent-edge reduction. -/
theorem mayerExpansionTerm_succ_abs_le_treeSum_rootedExpActivity (G : SimpleGraph ι)
    [Fintype G.edgeSet] (n : ℕ) (t : ℝ) :
    |mayerExpansionTerm G (n + 1) t| ≤
      (((n + 1).factorial : ℝ)⁻¹) *
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G),
          ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
            |t| ^ (ω 0).card *
              ∏ i : Fin n,
                Real.exp 1 ^ (ω (Fin.succ i)).card * |t| ^ (ω (Fin.succ i)).card := by
  refine (mayerExpansionTerm_abs_le_treeSum_activity G (n + 1) t).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum fun ω _ => ?_
  refine Finset.sum_le_sum fun T _ => ?_
  rw [Fin.prod_univ_succ]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
  refine le_mul_of_one_le_left (by positivity) ?_
  exact one_le_pow₀ (Real.one_le_exp_iff.mpr zero_le_one)

end IsingModel
