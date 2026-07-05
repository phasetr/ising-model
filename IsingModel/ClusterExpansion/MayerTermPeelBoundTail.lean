import IsingModel.ClusterExpansion.MayerCore.MayerTreeSumExpActivity
import IsingModel.ClusterExpansion.RootedParentActiveTreePeelBoundTail

/-!
# The Mayer term bounded by the (Δ²e|t|)^n-weighted summed peel bound (GJ §18.5)

The tail sharpening of `mayerExpansionTerm_succ_abs_le_sum_peelBound` (#4120): composing
the Penrose tree-graph bound on the Mayer expansion term (#4095) with the tail Penrose
tree-sum bound (`penroseTreeSum_le_sum_pow_peelBound`, #4132) bounds
`|mayerExpansionTerm G (n + 1) t|` by `(n + 1)!⁻¹` times the sum, over complete-graph
spanning-tree shapes, of `(Δ²e|t|)^n` times the child-count peel bound.

* `mayerExpansionTerm_succ_abs_le_sum_pow_peelBound`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A quantity bridged to the Penrose tree sum over an abstract polymer set is bounded by
the `(Δ²e|t|)^n`-weighted summed gas peel bound.**  Given `Δ²e|t| < 1`, a support-cardinality
bound `|supp P| ≤ c·|P|` on all `P ∈ 𝓟` with `0 ≤ c`, and a *bridge* `hbridge` bounding a
quantity `X` by `(n + 1)!⁻¹` times the Penrose tree-graph sum over `𝓟`, the quantity `X` is
at most `(n + 1)!⁻¹` times the sum, over complete-graph spanning-tree shapes `T`, of
`(Δ²e|t|)^n` times the child-count gas peel bound.  The bridge itself (from a Mayer-type term
to the tree sum) is supplied by the caller; here we only chain it with the tail leaf-peel
bridge `penroseGasTreeSum_le_sum_pow_peelBound`.  The even gas (`allPolymers G`, `c = 1`)
recovers `mayerExpansionTerm_succ_abs_le_sum_pow_peelBound`. -/
theorem le_sum_pow_rootedGasParentActivePeelBound_of_le_penroseTreeSum (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {𝓟 : Finset (Finset (Sym2 ι))}
    (hgas : PolymerGasData G 𝓟) (n : ℕ) {c : ℝ}
    (hsupp : ∀ P ∈ 𝓟, ((polymerSupport P).card : ℝ) ≤ c * (P.card : ℝ)) (hc : 0 ≤ c) {t : ℝ}
    {X : ℝ}
    (hbridge : X ≤ ((n + 1).factorial : ℝ)⁻¹
      * ∑ ω ∈ Fintype.piFinset (fun _ : Fin (n + 1) => 𝓟),
          ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
            |t| ^ (ω 0).card
              * ∏ i : Fin n, Real.exp 1 ^ (ω (Fin.succ i)).card * |t| ^ (ω (Fin.succ i)).card)
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    X ≤ ((n + 1).factorial : ℝ)⁻¹
        * ∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
            S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ n
            * rootedGasParentActivePeelBound G 𝓟 c (Penrose.completeGraphTreeParentCode n T)
                (Finset.univ : Finset (Fin n)) (fun _ => 0) t := by
  refine hbridge.trans ?_
  exact mul_le_mul_of_nonneg_left
    (penroseGasTreeSum_le_sum_pow_peelBound G hgas n hsupp hc hkp) (by positivity)

/-- **The Mayer term bounded by the `(Δ²e|t|)^n`-weighted summed peel bound.**  For
`Δ²e|t| < 1`, `|mayerExpansionTerm G (n + 1) t|` is at most `(n + 1)!⁻¹` times the sum,
over complete-graph spanning-tree shapes `T`, of `(Δ²e|t|)^n` times the child-count peel
bound.  Even-gas (`allPolymers G`, `c = 1`) instance of
`le_sum_pow_rootedGasParentActivePeelBound_of_le_penroseTreeSum`, with the Mayer→tree bridge
supplied by #4095. -/
theorem mayerExpansionTerm_succ_abs_le_sum_pow_peelBound (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (n : ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    |mayerExpansionTerm G (n + 1) t|
      ≤ ((n + 1).factorial : ℝ)⁻¹
        * ∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
            S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ n
            * rootedParentActivePeelBound G (Penrose.completeGraphTreeParentCode n T)
                (Finset.univ : Finset (Fin n)) (fun _ => 0) t := by
  have hsupp : ∀ P ∈ allPolymers G, ((polymerSupport P).card : ℝ) ≤ 1 * (P.card : ℝ) := by
    intro P hP; rw [one_mul]; exact_mod_cast polymerSupport_card_le_card_of_mem_allPolymers G hP
  exact le_sum_pow_rootedGasParentActivePeelBound_of_le_penroseTreeSum G (evenPolymerGasData G) n
    hsupp zero_le_one (mayerExpansionTerm_succ_abs_le_treeSum_rootedExpActivity G n t) hkp

end IsingModel
