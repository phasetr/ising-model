import IsingModel.ClusterExpansion.RootedParentActiveSum

/-!
# Splitting off a leaf vertex of the active set (GJ §18.5)

The leaf-peel induction step needs to peel the leaf coordinate `Fin.succ j` off the
active-vertex subtype.  The structural fact is that for an active vertex `j ∈ A`, the
active vertices of `A` are those of `A.erase j` together with the disjoint extra
vertex `Fin.succ j`:

* `rootedParentActiveVertices_insert_erase`:
  `rootedParentActiveVertices A = insert (Fin.succ j) (rootedParentActiveVertices (A.erase j))`.
* `succ_notMem_rootedParentActiveVertices_erase`:
  `Fin.succ j ∉ rootedParentActiveVertices (A.erase j)`.

Combined through `Finset.subtypeInsertEquivOption`, these give the equivalence

* `rootedParentActiveSplitEquiv`:
  `RootedParentActive A ≃ Option (RootedParentActive (A.erase j))`,

which sends the peeled vertex `Fin.succ j` to `none` and every other active vertex to
the corresponding vertex of `A.erase j`.  In the intended application `j` is a leaf of
`A`; the equivalence itself only needs `j ∈ A`.  This is the combinatorial backbone of
the coordinate split used to peel the leaf factor out of `rootedParentActiveSum`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {n : ℕ}

/-- **Splitting a constant `piFinset` sum along an `Option` equivalence.**  If the
index type `α` is equivalent to `Option β`, then a sum over labellings
`ω : α → X` (each coordinate ranging over a fixed finset `s`) splits as an outer sum
over the value `x ∈ s` at the `none` coordinate and an inner sum over the remaining
labellings `η : β → X`, with `ω` reconstructed by `(e a).elim x η`. -/
theorem sum_piFinset_const_optionEquiv {α β X : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ Option β) (s : Finset X) (f : (α → X) → ℝ) :
    ∑ ω ∈ Fintype.piFinset (fun _ : α => s), f ω
      = ∑ x ∈ s, ∑ η ∈ Fintype.piFinset (fun _ : β => s),
          f (fun a => (e a).elim x η) := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij'
    (fun ω _ => (ω (e.symm none), fun b => ω (e.symm (some b))))
    (fun p _ => fun a => (e a).elim p.1 p.2)
    (fun ω hω => ?_) (fun p hp => ?_) (fun ω hω => ?_) (fun p hp => ?_) (fun ω hω => ?_)
  · -- the image lands in `s ×ˢ piFinset`
    rw [Finset.mem_product]
    refine ⟨(Fintype.mem_piFinset.mp hω) _, Fintype.mem_piFinset.mpr fun b => ?_⟩
    exact (Fintype.mem_piFinset.mp hω) _
  · -- the inverse lands in `piFinset`
    rw [Finset.mem_product] at hp
    refine Fintype.mem_piFinset.mpr fun a => ?_
    change (e a).elim p.1 p.2 ∈ s
    cases e a with
    | none => exact hp.1
    | some b => exact (Fintype.mem_piFinset.mp hp.2) b
  · -- left inverse: reconstruct `ω`
    funext a
    rcases h : e a with _ | b
    · have ha : a = e.symm none := by rw [← h, Equiv.symm_apply_apply]
      simp [ha]
    · have ha : a = e.symm (some b) := by rw [← h, Equiv.symm_apply_apply]
      simp [ha]
  · -- right inverse: reconstruct `(x, η)`
    refine Prod.ext ?_ ?_
    · simp [Equiv.apply_symm_apply]
    · funext b
      simp [Equiv.apply_symm_apply]
  · -- value equality
    congr 1
    funext a
    rcases h : e a with _ | b
    · have ha : a = e.symm none := by rw [← h, Equiv.symm_apply_apply]
      simp [ha]
    · have ha : a = e.symm (some b) := by rw [← h, Equiv.symm_apply_apply]
      simp [ha]

/-- **The active vertices split off the leaf.**  For an active vertex `j ∈ A`, the
active vertices of `A` are the active vertices of `A.erase j` together with the leaf
vertex `Fin.succ j`. -/
theorem rootedParentActiveVertices_insert_erase {A : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ A) :
    rootedParentActiveVertices A
      = insert (Fin.succ j) (rootedParentActiveVertices (A.erase j)) := by
  rw [rootedParentActiveVertices, rootedParentActiveVertices,
    Finset.insert_comm,
    ← Finset.image_insert, Finset.insert_erase hj]

/-- **The leaf vertex is not an active vertex of the erased set.**  Since `j` is
erased, `Fin.succ j` is no longer active in `A.erase j`. -/
theorem succ_notMem_rootedParentActiveVertices_erase {A : Finset (Fin n)} {j : Fin n} :
    Fin.succ j ∉ rootedParentActiveVertices (A.erase j) := by
  rw [succ_mem_rootedParentActiveVertices]
  exact Finset.notMem_erase j A

/-- **The leaf-split equivalence.**  For an active vertex `j ∈ A` (the leaf in the
intended leaf-peel application), the active-vertex subtype of `A` is equivalent to
`Option` of the active-vertex subtype of `A.erase j`: the peeled vertex `Fin.succ j`
corresponds to `none` and every other active vertex to the corresponding vertex of
`A.erase j`. -/
noncomputable def rootedParentActiveSplitEquiv {A : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ A) :
    RootedParentActive A ≃ Option (RootedParentActive (A.erase j)) :=
  (Equiv.subtypeEquivRight (p := fun v => v ∈ rootedParentActiveVertices A) (fun v => by
        rw [rootedParentActiveVertices_insert_erase hj])).trans
    (Finset.subtypeInsertEquivOption succ_notMem_rootedParentActiveVertices_erase)

/-- The leaf-split equivalence sends `none` back to the peeled active vertex
`Fin.succ j`. -/
@[simp]
theorem rootedParentActiveSplitEquiv_symm_none_coe {A : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ A) :
    ((rootedParentActiveSplitEquiv hj).symm none : Fin (n + 1)) = Fin.succ j := rfl

/-- The leaf-split equivalence sends `some w` back to the underlying vertex of `w`. -/
@[simp]
theorem rootedParentActiveSplitEquiv_symm_some_coe {A : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ A) (w : RootedParentActive (A.erase j)) :
    ((rootedParentActiveSplitEquiv hj).symm (some w) : Fin (n + 1)) = w.1 := rfl

end IsingModel
