import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Rooted-parent active-set scaffolding for the leaf-peel induction (GJ §18.5)

The rooted-tree Kotecky--Preiss leaf-peel induction (FV Theorem 5.4) recurses by
removing a *leaf* of an active vertex set, rather than re-deriving the parent code of
a shrinking tree.  This file sets up the combinatorial scaffolding: an active set
`A : Finset (Fin n)` of non-root vertices (the root is the extra vertex `0` of
`Fin (n+1)`), a parent function `par : Fin n → Fin (n+1)`, and the predicates needed
to erase a leaf:

* `rootedParentActiveVertices A := insert 0 (A.image Fin.succ)` — the active vertices
  including the root `0`.
* `RootedParentActiveClosed par A` — every active non-root vertex's parent is active
  (or the root).
* `RootedParentLeaf par A j` — `j ∈ A` is a leaf: no active vertex has `Fin.succ j`
  as its parent.

The two structural facts needed for the induction step are that erasing a leaf
preserves active-closedness (`RootedParentActiveClosed.erase_leaf`) and that the
leaf's parent remains active after the erase (`RootedParentLeaf.parent_mem_erase`).

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {n : ℕ}

/-- The active vertices of `A` inside `Fin (n+1)`: the root `0` together with the
non-root active vertices `Fin.succ j` for `j ∈ A`. -/
def rootedParentActiveVertices (A : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  insert 0 (A.image Fin.succ)

/-- `Fin.succ j ∈ rootedParentActiveVertices A` iff `j ∈ A`. -/
theorem succ_mem_rootedParentActiveVertices {A : Finset (Fin n)} {j : Fin n} :
    Fin.succ j ∈ rootedParentActiveVertices A ↔ j ∈ A := by
  simp [rootedParentActiveVertices, Fin.succ_ne_zero, Finset.mem_image, Fin.succ_inj]

/-- The root `0` is always an active vertex. -/
@[simp]
theorem zero_mem_rootedParentActiveVertices (A : Finset (Fin n)) :
    (0 : Fin (n + 1)) ∈ rootedParentActiveVertices A :=
  Finset.mem_insert_self _ _

/-- **Active-closedness**: every active non-root vertex's parent is an active vertex. -/
def RootedParentActiveClosed (par : Fin n → Fin (n + 1)) (A : Finset (Fin n)) : Prop :=
  ∀ j ∈ A, par j ∈ rootedParentActiveVertices A

/-- **A leaf of the active set**: `j ∈ A` and no active vertex has `Fin.succ j` as its
parent. -/
def RootedParentLeaf (par : Fin n → Fin (n + 1)) (A : Finset (Fin n)) (j : Fin n) : Prop :=
  j ∈ A ∧ ∀ i ∈ A, par i ≠ Fin.succ j

/-- **Erasing a leaf preserves active-closedness.**  If `A` is active-closed and `j`
is a leaf, then `A.erase j` is active-closed: an active vertex `i ≠ j` has its parent
still active in `A.erase j` (its parent cannot be `Fin.succ j`, since `j` is a leaf). -/
theorem RootedParentActiveClosed.erase_leaf {par : Fin n → Fin (n + 1)}
    {A : Finset (Fin n)} {j : Fin n} (hclosed : RootedParentActiveClosed par A)
    (hleaf : RootedParentLeaf par A j) :
    RootedParentActiveClosed par (A.erase j) := by
  intro i hi
  rw [Finset.mem_erase] at hi
  have hpar := hclosed i hi.2
  rw [rootedParentActiveVertices, Finset.mem_insert, Finset.mem_image] at hpar ⊢
  rcases hpar with h0 | ⟨m, hmA, hmeq⟩
  · exact Or.inl h0
  · refine Or.inr ⟨m, ?_, hmeq⟩
    rw [Finset.mem_erase]
    refine ⟨fun hmj => hleaf.2 i hi.2 ?_, hmA⟩
    rw [← hmeq, hmj]

/-- **The leaf's parent remains active after erasing the leaf.**  If `A` is
active-closed and `j` is a leaf, then `par j` is an active vertex of `A.erase j`
(`par j` cannot be `Fin.succ j`, since `j` is a leaf in `A`). -/
theorem RootedParentLeaf.parent_mem_erase {par : Fin n → Fin (n + 1)}
    {A : Finset (Fin n)} {j : Fin n} (hclosed : RootedParentActiveClosed par A)
    (hleaf : RootedParentLeaf par A j) :
    par j ∈ rootedParentActiveVertices (A.erase j) := by
  have hpar := hclosed j hleaf.1
  rw [rootedParentActiveVertices, Finset.mem_insert, Finset.mem_image] at hpar ⊢
  rcases hpar with h0 | ⟨m, hmA, hmeq⟩
  · exact Or.inl h0
  · refine Or.inr ⟨m, ?_, hmeq⟩
    rw [Finset.mem_erase]
    refine ⟨fun hmj => hleaf.2 j hleaf.1 ?_, hmA⟩
    rw [← hmeq, hmj]

end IsingModel
