import IsingModel.ClusterExpansion.RootedParentActiveLeafPeelTree

/-!
# Reindexing the full active-vertex labellings to `Fin (n + 1)` (GJ §18.5)

To feed the rooted-tree active sum into the Penrose tree-graph bound on
`mayerExpansionTerm` (whose labellings are `ω : Fin (n + 1) → allPolymers G`), the
active-vertex subtype of the full active set must be reindexed to `Fin (n + 1)`.  Since
`rootedParentActiveVertices Finset.univ = Finset.univ`, the active-vertex subtype is
just `Fin (n + 1)`.

* `sum_piFinset_const_domEquiv`: a constant-`piFinset` sum is invariant under reindexing
  the coordinate type along an equivalence `e : α ≃ β`.
* `rootedParentActiveUnivEquiv : RootedParentActive Finset.univ ≃ Fin (n + 1)`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {n : ℕ}

/-- **Reindexing a constant `piFinset` sum along a coordinate equivalence.**  If the
coordinate type `α` is equivalent to `β`, a sum over labellings `ω : α → X` (each
coordinate ranging over a fixed finset `s`) is unchanged by precomposing with the
equivalence: `∑_ω f ω = ∑_{ω'} f (ω' ∘ e)`. -/
theorem sum_piFinset_const_domEquiv {α β X : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (s : Finset X) (f : (α → X) → ℝ) :
    ∑ ω ∈ Fintype.piFinset (fun _ : α => s), f ω
      = ∑ ω ∈ Fintype.piFinset (fun _ : β => s), f (fun a => ω (e a)) := by
  refine Finset.sum_bij' (fun ω _ => fun b => ω (e.symm b)) (fun ω _ => fun a => ω (e a))
    (fun ω hω => ?_) (fun ω hω => ?_) (fun ω hω => ?_) (fun ω hω => ?_) (fun ω hω => ?_)
  · exact Fintype.mem_piFinset.mpr fun b => (Fintype.mem_piFinset.mp hω) _
  · exact Fintype.mem_piFinset.mpr fun a => (Fintype.mem_piFinset.mp hω) _
  · funext a; simp only [Equiv.symm_apply_apply]
  · funext b; simp only [Equiv.apply_symm_apply]
  · exact congrArg f (funext fun a => by simp only [Equiv.symm_apply_apply])

/-- **The full active-vertex subtype is `Fin (n + 1)`.**  Since
`rootedParentActiveVertices Finset.univ = Finset.univ`, the active-vertex subtype of the
full active set is equivalent to `Fin (n + 1)` (via the underlying coercion). -/
def rootedParentActiveUnivEquiv :
    RootedParentActive (Finset.univ : Finset (Fin n)) ≃ Fin (n + 1) :=
  Equiv.subtypeUnivEquiv fun v => by
    rw [rootedParentActiveVertices_univ]; exact Finset.mem_univ v

/-- The univ reindex equivalence is the underlying coercion. -/
@[simp]
theorem rootedParentActiveUnivEquiv_apply
    (v : RootedParentActive (Finset.univ : Finset (Fin n))) :
    rootedParentActiveUnivEquiv v = (v : Fin (n + 1)) := rfl

/-- The inverse of the univ reindex equivalence injects `Fin (n + 1)` back into the
active-vertex subtype. -/
@[simp]
theorem rootedParentActiveUnivEquiv_symm_apply_coe (a : Fin (n + 1)) :
    ((rootedParentActiveUnivEquiv.symm a : RootedParentActive (Finset.univ : Finset (Fin n)))
      : Fin (n + 1)) = a := rfl

end IsingModel
