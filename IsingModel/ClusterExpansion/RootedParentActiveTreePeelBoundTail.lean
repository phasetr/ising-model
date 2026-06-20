import IsingModel.ClusterExpansion.RootedParentActiveTreeBridge
import IsingModel.ClusterExpansion.RootedParentActiveUnivForm
import IsingModel.ClusterExpansion.RootedParentActiveLeafPeelTailTree

/-!
# The Penrose tree sum bounded by the (Δ²e|t|)^n-weighted peel bound (GJ §18.5)

The tail sharpening of `penroseTreeSum_le_sum_peelBound` (#4119): using the sharpened
(tail) tree leaf-peel bound (#4130,
`rootedParentActiveSum_completeGraphTreeParentCode_univ_zero_le_pow_mul_peelBound`) at the
final step bounds the Penrose tree-graph sum by the sum over complete-graph spanning-tree
shapes of `(Δ²e|t|)^n` times the child-count peel bound (one `Δ²e|t|` per non-root vertex).

* `penroseTreeSum_le_sum_pow_peelBound`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Penrose tree sum is bounded by the `(Δ²e|t|)^n`-weighted summed peel bound.**
The tail sharpening of `penroseTreeSum_le_sum_peelBound`: per shape, the rooted-tree active
sum is bounded by `(Δ²e|t|)^n` times the child-count peel bound (the tail leaf-peel
induction #4130), giving the Penrose tree-graph sum a `(Δ²e|t|)^n` factor per shape. -/
theorem penroseTreeSum_le_sum_pow_peelBound (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (n : ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    (∑ ω ∈ Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G),
        ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
          |t| ^ (ω 0).card
            * ∏ i : Fin n, Real.exp 1 ^ (ω (Fin.succ i)).card * |t| ^ (ω (Fin.succ i)).card)
      ≤ ∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
            S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ n
            * rootedParentActivePeelBound G (Penrose.completeGraphTreeParentCode n T)
                (Finset.univ : Finset (Fin n)) (fun _ => 0) t := by
  -- The Penrose summand is dominated by the uniform activity product.
  have hWle : ∀ ω : Fin (n + 1) → Finset (Sym2 ι),
      |t| ^ (ω 0).card
          * ∏ i : Fin n, Real.exp 1 ^ (ω (Fin.succ i)).card * |t| ^ (ω (Fin.succ i)).card
        ≤ ∏ v : Fin (n + 1), (Real.exp 1 * |t|) ^ (ω v).card := by
    intro ω
    rw [Fin.prod_univ_succ,
      Finset.prod_congr rfl (g := fun i : Fin n => (Real.exp 1 * |t|) ^ (ω (Fin.succ i)).card)
        fun i _ => (mul_pow _ _ _).symm]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine pow_le_pow_left₀ (abs_nonneg t) ?_ _
    exact le_mul_of_one_le_left (abs_nonneg t) (Real.one_le_exp_iff.mpr zero_le_one)
  refine (penroseTreeSum_le_subtype_parentConstraint G n
    (fun ω => |t| ^ (ω 0).card
      * ∏ i : Fin n, Real.exp 1 ^ (ω (Fin.succ i)).card * |t| ^ (ω (Fin.succ i)).card)
    (fun ω => by positivity)).trans ?_
  refine Finset.sum_le_sum fun T _ => ?_
  calc
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
        (fun ω => ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i))
          (ω (Penrose.completeGraphTreeParentCode n T i))),
        |t| ^ (ω 0).card
          * ∏ i : Fin n, Real.exp 1 ^ (ω (Fin.succ i)).card * |t| ^ (ω (Fin.succ i)).card)
        ≤ ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
            (fun ω => ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i))
              (ω (Penrose.completeGraphTreeParentCode n T i))),
            ∏ v : Fin (n + 1), (Real.exp 1 * |t|) ^ (ω v).card :=
          Finset.sum_le_sum fun ω _ => hWle ω
    _ = ∑ ω ∈ Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G),
          if ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i))
              (ω (Penrose.completeGraphTreeParentCode n T i)) then
            ∏ v : Fin (n + 1), (Real.exp 1 * |t|) ^ (ω v).card else 0 :=
          Finset.sum_filter _ _
    _ = rootedParentActiveSum G (Penrose.completeGraphTreeParentCode n T)
          (Finset.univ : Finset (Fin n))
          (rootedParentActiveClosed_univ (Penrose.completeGraphTreeParentCode n T))
          (fun _ => 0) t :=
          (rootedParentActiveSum_univ_zero_eq G (Penrose.completeGraphTreeParentCode n T) t).symm
    _ ≤ ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ n
          * rootedParentActivePeelBound G (Penrose.completeGraphTreeParentCode n T)
              (Finset.univ : Finset (Fin n)) (fun _ => 0) t :=
          rootedParentActiveSum_completeGraphTreeParentCode_univ_zero_le_pow_mul_peelBound G n T hkp

end IsingModel
