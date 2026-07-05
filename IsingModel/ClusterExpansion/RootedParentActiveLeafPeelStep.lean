import IsingModel.ClusterExpansion.RootedParentActiveLeafInner

/-!
# The leaf-peel decomposition of the active sum (GJ §18.5)

Summing the per-labelling leaf isolation (`rootedParentActiveSum_leaf_inner`) over the
remainder labellings `η` gives the full leaf-peel decomposition of
`rootedParentActiveSum`: for a leaf `j`,

`rootedParentActiveSum G par A hclosed k t`
` = ∑_η (remainder summand at η) · leafColumnSum G (η ⟨par j, _⟩) (k (succ j)) t`,

where the remainder summand is the `rootedParentActiveSum` summand for `A.erase j` at
`η`.  The proof applies `sum_piFinset_const_optionEquiv` (splitting the leaf coordinate
off the active-vertex labelling), commutes the two sums, and rewrites each inner sum by
`rootedParentActiveSum_leaf_inner`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **The leaf-peel decomposition of the active gas sum.**  For a leaf `j` of an
active-closed set `A`, the active gas sum over `A` decomposes as a sum over the remainder
labellings `η` of the active vertices of `A.erase j`, each weighted by the leaf column gas
sum at the remainder value `η ⟨par j, _⟩` assigned to the leaf's parent vertex.  The
remainder summand is exactly the `rootedGasParentActiveSum` summand for `A.erase j` at
`η`.  The even gas (`allPolymers G`) is recovered by `rootedParentActiveSum_leaf_peel`. -/
theorem rootedGasParentActiveSum_leaf_peel (G : SimpleGraph ι) [Fintype G.edgeSet]
    (𝓟 : Finset (Finset (Sym2 ι))) {par : Fin n → Fin (n + 1)} {A : Finset (Fin n)} {j : Fin n}
    (hclosed : RootedParentActiveClosed par A) (hleaf : RootedParentLeaf par A j)
    (k : Fin (n + 1) → ℕ) (t : ℝ) :
    rootedGasParentActiveSum G 𝓟 par A hclosed k t
      = ∑ η ∈ Fintype.piFinset (fun _ : RootedParentActive (A.erase j) => 𝓟),
          (if ∀ i, ∀ hi : i ∈ A.erase j,
              PolymersIncompatible (η (rootedParentActiveChild hi))
                (η (rootedParentActiveParent (hclosed.erase_leaf hleaf) hi)) then
            ∏ w : RootedParentActive (A.erase j),
              ((η w).card : ℝ) ^ k w.1 * (Real.exp 1 * |t|) ^ (η w).card
          else 0)
          * leafGasColumnSum 𝓟 (η ⟨par j, hleaf.parent_mem_erase hclosed⟩) (k (Fin.succ j)) t := by
  rw [rootedGasParentActiveSum,
    sum_piFinset_const_optionEquiv (rootedParentActiveSplitEquiv hleaf.1) 𝓟,
    Finset.sum_comm]
  exact Finset.sum_congr rfl fun η _ => rootedGasParentActiveSum_leaf_inner 𝓟 hclosed hleaf k t η

/-- **The leaf-peel decomposition of the active sum.**  Even-gas (`allPolymers G`) instance
of `rootedGasParentActiveSum_leaf_peel`. -/
theorem rootedParentActiveSum_leaf_peel (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] {par : Fin n → Fin (n + 1)} {A : Finset (Fin n)} {j : Fin n}
    (hclosed : RootedParentActiveClosed par A) (hleaf : RootedParentLeaf par A j)
    (k : Fin (n + 1) → ℕ) (t : ℝ) :
    rootedParentActiveSum G par A hclosed k t
      = ∑ η ∈ Fintype.piFinset (fun _ : RootedParentActive (A.erase j) => allPolymers G),
          (if ∀ i, ∀ hi : i ∈ A.erase j,
              PolymersIncompatible (η (rootedParentActiveChild hi))
                (η (rootedParentActiveParent (hclosed.erase_leaf hleaf) hi)) then
            ∏ w : RootedParentActive (A.erase j),
              ((η w).card : ℝ) ^ k w.1 * (Real.exp 1 * |t|) ^ (η w).card
          else 0)
          * leafColumnSum G (η ⟨par j, hleaf.parent_mem_erase hclosed⟩) (k (Fin.succ j)) t :=
  rootedGasParentActiveSum_leaf_peel G (allPolymers G) hclosed hleaf k t

end IsingModel
