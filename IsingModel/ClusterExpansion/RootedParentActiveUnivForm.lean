import IsingModel.ClusterExpansion.RootedParentActiveUnivReindex

/-!
# The univ rooted-tree active sum in `Fin (n + 1)`-labelling form (GJ §18.5)

Reindexing the full active-vertex labellings to `Fin (n + 1)` (#4116) rewrites the
rooted-tree active sum over `Finset.univ` at exponent `0` into the explicit
`Fin (n + 1)`-labelling form used by the Penrose tree-graph bound: a sum over polymer
sequences `ω : Fin (n + 1) → allPolymers G` with the parent-edge incompatibility
constraint and the (unweighted, exponent `0`) activity product.

* `rootedParentActiveSum_univ_zero_eq`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **The univ rooted-tree active sum as a `Fin (n + 1)`-labelling sum.**  For the full
active set and any parent function, the rooted-tree active sum at exponent `0` is the
sum over polymer sequences `ω : Fin (n + 1) → allPolymers G` of the activity product
`∏_v (e|t|)^{|ω v|}`, restricted to the parent-edge incompatibility constraint
`ω (Fin.succ i) ∼ ω (par i)` for every `i`.  (The labellings are reindexed from the
active-vertex subtype to `Fin (n + 1)` via `rootedParentActiveUnivEquiv`; the exponent
`0` makes the moment factors trivial.) -/
theorem rootedParentActiveSum_univ_zero_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (par : Fin n → Fin (n + 1)) (t : ℝ) :
    rootedParentActiveSum G par (Finset.univ : Finset (Fin n))
        (rootedParentActiveClosed_univ par) (fun _ => 0) t
      = ∑ ω ∈ Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G),
          if ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i)) (ω (par i)) then
            ∏ v : Fin (n + 1), (Real.exp 1 * |t|) ^ (ω v).card
          else 0 := by
  rw [rootedParentActiveSum,
    sum_piFinset_const_domEquiv rootedParentActiveUnivEquiv (allPolymers G)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  refine if_congr ?_ ?_ rfl
  · constructor
    · intro h i
      have := h i (Finset.mem_univ i)
      simpa [rootedParentActiveChild, rootedParentActiveParent,
        rootedParentActiveUnivEquiv_apply] using this
    · intro h j _
      have := h j
      simpa [rootedParentActiveChild, rootedParentActiveParent,
        rootedParentActiveUnivEquiv_apply] using this
  · rw [← Equiv.prod_comp rootedParentActiveUnivEquiv
      (fun a => (Real.exp 1 * |t|) ^ (ω a).card)]
    refine Finset.prod_congr rfl fun v _ => ?_
    simp [rootedParentActiveUnivEquiv_apply]

end IsingModel
