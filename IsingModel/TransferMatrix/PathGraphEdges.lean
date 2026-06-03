import IsingModel.GibbsMeasure
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Edge enumeration of the open path graph (GJ §17.1)

Mathlib provides the adjacency relation `pathGraph_adj` of the open path graph
`pathGraph n` on `Fin n` but not its edge set as an explicit `Finset`.  This file
enumerates the `n` edges of `pathGraph (n+1)` as the consecutive pairs
`s(i.castSucc, i.succ)` for `i : Fin n`, the open-chain analogue of the cyclic
enumeration `cycleGraph_edgeFinset_eq_image` (#3518).

This is the combinatorial foundation for the exact open-chain two-point function
`⟨σ₀σₙ⟩ = (tanh βJ)ⁿ` via the FV (3.46) high-temperature expansion (the open path
is a tree, so its even-subgraph denominator collapses to `1`).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators
open SimpleGraph

/-- Adjacency in the open path graph is decidable (it is a `Fin`-value equation). -/
instance pathGraph_decidableAdj (n : ℕ) : DecidableRel (pathGraph n).Adj :=
  fun _ _ => decidable_of_iff _ pathGraph_adj.symm

/-- The open path graph on `Fin n` has a (computable) finite edge set. -/
instance pathGraph_fintypeEdgeSet (n : ℕ) : Fintype (pathGraph n).edgeSet :=
  SimpleGraph.fintypeEdgeSet (pathGraph n)

/-- The consecutive-pair edge `s(i.castSucc, i.succ)` of the open path. -/
private def pathPair {n : ℕ} (i : Fin n) : Sym2 (Fin (n + 1)) :=
  s(i.castSucc, i.succ)

/-- **Adjacency of `pathGraph (n+1)` for consecutive `Fin n`-indexed vertices**:
`(pathGraph (n+1)).Adj i.castSucc i.succ`. -/
theorem pathGraph_adj_castSucc_succ {n : ℕ} (i : Fin n) :
    (pathGraph (n + 1)).Adj i.castSucc i.succ := by
  rw [pathGraph_adj]
  left
  rw [Fin.val_castSucc, Fin.val_succ]

/-- **Edge enumeration of the open path graph** (Glimm–Jaffe §17.1): the edge set of
`pathGraph (n+1)` is the image of the `n` consecutive pairs
`i ↦ s(i.castSucc, i.succ)`,
`(pathGraph (n+1)).edgeFinset = image (fun i : Fin n => s(i.castSucc, i.succ)) univ`. -/
theorem pathGraph_edgeFinset_eq_image (n : ℕ) :
    (pathGraph (n + 1)).edgeFinset
      = Finset.image (fun i : Fin n => s(i.castSucc, i.succ)) Finset.univ := by
  ext e
  refine Sym2.ind (fun a b => ?_) e
  rw [mem_edgeFinset, mem_edgeSet, pathGraph_adj, Finset.mem_image]
  constructor
  · rintro (h | h)
    · -- a.val + 1 = b.val, so a = i.castSucc, b = i.succ with i.val = a.val
      have ha : a.val < n := by omega
      refine ⟨⟨a.val, ha⟩, Finset.mem_univ _, ?_⟩
      rw [Sym2.eq_iff]
      left
      refine ⟨?_, ?_⟩
      · ext; rw [Fin.val_castSucc]
      · ext; rw [Fin.val_succ]; omega
    · have hb : b.val < n := by omega
      refine ⟨⟨b.val, hb⟩, Finset.mem_univ _, ?_⟩
      rw [Sym2.eq_iff]
      right
      refine ⟨?_, ?_⟩
      · ext; rw [Fin.val_castSucc]
      · ext; rw [Fin.val_succ]; omega
  · rintro ⟨i, _, hi⟩
    rw [Sym2.eq_iff] at hi
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; rw [Fin.val_castSucc, Fin.val_succ]
    · right; rw [Fin.val_castSucc, Fin.val_succ]

/-- The consecutive-pair map `i ↦ s(i.castSucc, i.succ)` is injective on `Fin n`
(the open path has no repeated edges). -/
theorem pathPair_injective (n : ℕ) :
    Function.Injective (fun i : Fin n => s(i.castSucc, i.succ)) := by
  intro i j hij
  rw [Sym2.eq_iff] at hij
  rcases hij with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact Fin.castSucc_injective n h1
  · -- i.castSucc = j.succ ∧ i.succ = j.castSucc forces i.val = j.val+1 = i.val+2, impossible
    exfalso
    have hi : i.val = j.val + 1 := by
      have := congrArg Fin.val h1
      rwa [Fin.val_castSucc, Fin.val_succ] at this
    have hj : i.val + 1 = j.val := by
      have := congrArg Fin.val h2
      rwa [Fin.val_succ, Fin.val_castSucc] at this
    omega

/-- The open path graph `pathGraph (n+1)` has `n` edges. -/
theorem card_pathGraph_edgeFinset (n : ℕ) :
    (pathGraph (n + 1)).edgeFinset.card = n := by
  rw [pathGraph_edgeFinset_eq_image,
    Finset.card_image_of_injective _ (pathPair_injective n), Finset.card_univ,
    Fintype.card_fin]

/-- **Product over open-path edges as a linear product over `Fin n`**: for any
commutative monoid, `∏_{e ∈ (pathGraph (n+1)).edgeFinset} f e = ∏_i f s(i.castSucc, i.succ)`. -/
theorem prod_pathGraph_edgeFinset {M : Type*} [CommMonoid M] (n : ℕ)
    (f : Sym2 (Fin (n + 1)) → M) :
    ∏ e ∈ (pathGraph (n + 1)).edgeFinset, f e
      = ∏ i : Fin n, f s(i.castSucc, i.succ) := by
  rw [pathGraph_edgeFinset_eq_image,
    Finset.prod_image (fun i _ j _ h => pathPair_injective n h)]

end TransferMatrix

end IsingModel
