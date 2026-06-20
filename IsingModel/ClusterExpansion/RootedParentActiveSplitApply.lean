import IsingModel.ClusterExpansion.RootedParentActiveSplit

/-!
# Forward action of the leaf-split equivalence (GJ §18.5)

The leaf-peel assembly reconstructs a labelling `ω` of the active vertices of `A` from
a leaf value `x` and a labelling `η` of the active vertices of `A.erase j`, via the
form `ω v = (rootedParentActiveSplitEquiv hj v).elim x η` produced by
`sum_piFinset_const_optionEquiv`.  To identify `ω` at the leaf vertex and at the
remaining vertices we need the *forward* action of the split equivalence (the
`symm`-coercions already record the inverse):

* `rootedParentActiveSplitEquiv_child`: the peeled vertex `Fin.succ j` maps to `none`.
* `rootedParentActiveSplitEquiv_apply_some`: every other active vertex `v` (with
  `↑v ∈ rootedParentActiveVertices (A.erase j)`) maps to `some ⟨↑v, _⟩`.

The two reconstruction-evaluation lemmas `..._recon_child` / `..._recon_some` then read
off `ω (child j) = x` and `ω v = η ⟨↑v, _⟩`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {n : ℕ}

/-- **The peeled vertex maps to `none`.**  The leaf-split equivalence sends the active
child vertex `Fin.succ j` to `none`. -/
@[simp]
theorem rootedParentActiveSplitEquiv_child {A : Finset (Fin n)} {j : Fin n} (hj : j ∈ A) :
    rootedParentActiveSplitEquiv hj (rootedParentActiveChild hj) = none := by
  have h : rootedParentActiveChild hj = (rootedParentActiveSplitEquiv hj).symm none :=
    Subtype.ext (by simp)
  rw [h, Equiv.apply_symm_apply]

/-- **Every non-peeled active vertex maps to `some`.**  If the underlying vertex of `v`
is an active vertex of `A.erase j`, the leaf-split equivalence sends `v` to
`some ⟨↑v, _⟩`. -/
theorem rootedParentActiveSplitEquiv_apply_some {A : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ A) {v : RootedParentActive A}
    (hmem : (v : Fin (n + 1)) ∈ rootedParentActiveVertices (A.erase j)) :
    rootedParentActiveSplitEquiv hj v = some ⟨v, hmem⟩ := by
  rw [Equiv.apply_eq_iff_eq_symm_apply]
  exact Subtype.ext (by simp)

/-- **Reconstruction at the leaf vertex.**  The labelling reconstructed from a leaf
value `x` and a remainder labelling `η` takes the value `x` at the peeled vertex. -/
theorem rootedParentActiveSplitEquiv_recon_child {A : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ A) {X : Type*} (x : X) (η : RootedParentActive (A.erase j) → X) :
    (rootedParentActiveSplitEquiv hj (rootedParentActiveChild hj)).elim x η = x := by
  rw [rootedParentActiveSplitEquiv_child]
  rfl

/-- **Reconstruction at a remainder vertex.**  The labelling reconstructed from a
leaf value `x` and a remainder labelling `η` takes the value `η ⟨↑v, _⟩` at every
active vertex `v` other than the peeled one — i.e. whose underlying vertex is active in
`A.erase j` (such a `v` may itself be a leaf in the parent structure). -/
theorem rootedParentActiveSplitEquiv_recon_some {A : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ A) {X : Type*} (x : X) (η : RootedParentActive (A.erase j) → X)
    {v : RootedParentActive A}
    (hmem : (v : Fin (n + 1)) ∈ rootedParentActiveVertices (A.erase j)) :
    (rootedParentActiveSplitEquiv hj v).elim x η = η ⟨v, hmem⟩ := by
  rw [rootedParentActiveSplitEquiv_apply_some hj hmem]
  rfl

end IsingModel
