import IsingModel.ClusterExpansion.RootedParentActiveSplit

/-!
# Peeling the leaf factor out of the active product (GJ §18.5)

The leaf-peel inductive step rewrites a product over the active-vertex subtype of `A`
as the leaf factor (at the peeled vertex `Fin.succ j`) times the product over the
active-vertex subtype of `A.erase j`, transported along the leaf-split equivalence
`rootedParentActiveSplitEquiv`.

* `prod_rootedParentActive_eq_mul`: `∏_{v} g v = g (child j) · ∏_{w} g (embed w)`,
  where `embed w = (rootedParentActiveSplitEquiv hj).symm (some w)` lifts an active
  vertex of `A.erase j` back into the active-vertex subtype of `A`.
* `forall_mem_constraint_iff_erase`: the incompatibility constraints indexed by `A`
  factor as the single constraint at `j` together with those indexed by `A.erase j`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **Factoring the active constraints through a leaf erase.**  For an active vertex
`j ∈ A`, the incompatibility constraints `ω (succ i) ∼ ω (par i)` ranging over all
active `i ∈ A` are equivalent to the single constraint at `j` together with those
ranging over `A.erase j`.  This is the `Finset.forall_mem_insert` split of the active
set `A = insert j (A.erase j)`; the membership proofs in `rootedParentActiveChild` /
`rootedParentActiveParent` are irrelevant, so the constraints at `i ∈ A.erase j`
(lifted via `Finset.mem_of_mem_erase`) coincide with those at `i ∈ A`. -/
theorem forall_mem_constraint_iff_erase {par : Fin n → Fin (n + 1)}
    {A : Finset (Fin n)} {j : Fin n} (hclosed : RootedParentActiveClosed par A)
    (hj : j ∈ A) (ω : RootedParentActive A → Finset (Sym2 ι)) :
    (∀ i, ∀ hi : i ∈ A,
        PolymersIncompatible (ω (rootedParentActiveChild hi))
          (ω (rootedParentActiveParent hclosed hi)))
      ↔ PolymersIncompatible (ω (rootedParentActiveChild hj))
            (ω (rootedParentActiveParent hclosed hj))
        ∧ ∀ i, ∀ hi : i ∈ A.erase j,
            PolymersIncompatible (ω (rootedParentActiveChild (Finset.mem_of_mem_erase hi)))
              (ω (rootedParentActiveParent hclosed (Finset.mem_of_mem_erase hi))) := by
  constructor
  · intro h
    exact ⟨h j hj, fun i hi => h i (Finset.mem_of_mem_erase hi)⟩
  · rintro ⟨hleaf, hrest⟩ i hi
    rcases eq_or_ne i j with rfl | hne
    · exact hleaf
    · exact hrest i (Finset.mem_erase.mpr ⟨hne, hi⟩)

/-- **Peeling the leaf factor out of the active product.**  For an active vertex
`j ∈ A`, a product over the active-vertex subtype of `A` factors as the value at the
peeled vertex `Fin.succ j` (`rootedParentActiveChild hj`) times the product over the
active-vertex subtype of `A.erase j`, each vertex lifted back into the subtype of `A`
through `(rootedParentActiveSplitEquiv hj).symm ∘ some`. -/
theorem prod_rootedParentActive_eq_mul {A : Finset (Fin n)} {j : Fin n} (hj : j ∈ A)
    {M : Type*} [CommMonoid M] (g : RootedParentActive A → M) :
    ∏ v : RootedParentActive A, g v
      = g (rootedParentActiveChild hj) *
        ∏ w : RootedParentActive (A.erase j),
          g ((rootedParentActiveSplitEquiv hj).symm (some w)) := by
  rw [← Equiv.prod_comp (rootedParentActiveSplitEquiv hj).symm g, Fintype.prod_option,
    show (rootedParentActiveSplitEquiv hj).symm none = rootedParentActiveChild hj from
      Subtype.ext (by simp)]

end IsingModel
