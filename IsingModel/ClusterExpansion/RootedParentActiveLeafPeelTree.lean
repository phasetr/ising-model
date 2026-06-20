import IsingModel.ClusterExpansion.RootedParentActiveLeafPeelInduction
import IsingModel.ClusterExpansion.RootedParentLeafExistence

/-!
# The leaf-peel bound for the complete-graph spanning-tree parent code (GJ §18.5)

Specialising the leaf-peel induction bound (`rootedParentActiveSum_le_childCount_bound`)
to the full active set `Finset.univ` and the complete-graph spanning-tree parent code
discharges the leaf-existence hypothesis (every nonempty active set has a leaf, since
the parent code strictly decreases the tree distance from the root) and gives a
concrete bound on the rooted-tree active sum that the Penrose tree-graph bound on
`mayerExpansionTerm` feeds into.

* `rootedParentActiveVertices_univ`, `rootedParentActiveClosed_univ`.
* `rootedParentActiveSum_completeGraphTreeParentCode_univ_zero_le_peelBound`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset SimpleGraph

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The active vertices of the full active set are all of `Fin (n + 1)`: the root `0`
together with `Fin.succ i` for every `i` exhaust `Fin (n + 1)`. -/
theorem rootedParentActiveVertices_univ :
    rootedParentActiveVertices (Finset.univ : Finset (Fin n)) = Finset.univ := by
  rw [rootedParentActiveVertices]
  ext v
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, iff_true]
  obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ v
  · exact Or.inl rfl
  · exact Or.inr ⟨i, rfl⟩

/-- The full active set is active-closed for any parent function (every parent lands in
the full active-vertex set, which is all of `Fin (n + 1)`). -/
theorem rootedParentActiveClosed_univ (par : Fin n → Fin (n + 1)) :
    RootedParentActiveClosed par (Finset.univ : Finset (Fin n)) := by
  intro j _
  rw [rootedParentActiveVertices_univ]
  exact Finset.mem_univ _

/-- **The leaf-peel bound for the complete-graph spanning-tree parent code.**  For the
full active set and the parent code of a spanning tree `T` of the complete graph on
`Fin (n + 1)`, with `Δ²·e·|t| < 1`, the rooted-tree active sum (at exponent `0`) is
bounded by the child-count peel bound.  Leaf existence is discharged by
`completeGraphTreeParentCode_exists_active_leaf` (the parent code strictly decreases the
tree distance from the root). -/
theorem rootedParentActiveSum_completeGraphTreeParentCode_univ_zero_le_peelBound
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] (n : ℕ)
    (T : {S : Finset (Sym2 (Fin (n + 1))) //
      S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))}) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    rootedParentActiveSum G (Penrose.completeGraphTreeParentCode n T)
        (Finset.univ : Finset (Fin n))
        (rootedParentActiveClosed_univ (Penrose.completeGraphTreeParentCode n T))
        (fun _ => 0) t
      ≤ rootedParentActivePeelBound G (Penrose.completeGraphTreeParentCode n T)
          (Finset.univ : Finset (Fin n)) (fun _ => 0) t :=
  rootedParentActiveSum_le_childCount_bound G
    (fun hB => completeGraphTreeParentCode_exists_active_leaf hB T)
    (Finset.univ : Finset (Fin n))
    (rootedParentActiveClosed_univ (Penrose.completeGraphTreeParentCode n T)) (fun _ => 0) hkp

end IsingModel
