import IsingModel.ClusterExpansion.AlternatingCompleteGraph
import IsingModel.TransferMatrix.CycleGraphLink
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# General closed form for the cycle-graph alternating connected-spanning sum

This file proves the general-`n` closed form

  `alternatingConnectedSubgraphSum (cycleGraph n) = (-1)^(n-1) · (n-1)`  (`3 ≤ n`),

replacing the previous family of per-`n` `decide`-based lemmas (which only covered
`n = 3, …, 7` and required raised `maxHeartbeats`/`maxRecDepth` budgets).

The combinatorics is that a connected spanning subgraph of the cycle on `n`
vertices is either the full cycle (one subset of size `n`) or the cycle with a
single edge removed (`n` subsets of size `n-1`); every smaller subset is
disconnected.  Hence

  `∑ (-1)^|S| = (-1)^n + n·(-1)^(n-1) = (-1)^(n-1)·(n-1)`.

The technical heart is `cycleGraph_fromEdgeSet_erase_connected`: deleting any one
edge of the cycle keeps it connected.  This is proved by a rotation (translation)
automorphism reducing an arbitrary edge to the "wrap" edge `s(0, last)`, whose
deletion leaves the path graph, which is connected (`pathGraph_preconnected`).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4 (Mayer / cluster expansion).
-/

namespace IsingModel

open Finset SimpleGraph

/-- **Translation invariance of single-edge deletion connectivity** for the cycle
graph: if deleting the edge `f` from `cycleGraph (m+3)` leaves a connected graph,
then so does deleting the rotated edge `Sym2.map (· + d) f`.  The rotation
`x ↦ x + d` is a graph automorphism of `cycleGraph (m+3) = circulantGraph {1}`
(`circulantGraph_adj_translate`), and it carries the deleted singleton edge
accordingly, so connectivity transfers via `SimpleGraph.Iso.connected_iff`. -/
private theorem deleteEdges_translate_connected (m : ℕ) (d : Fin (m + 3))
    (f : Sym2 (Fin (m + 3)))
    (h : ((cycleGraph (m + 3)).deleteEdges {f}).Connected) :
    ((cycleGraph (m + 3)).deleteEdges {Sym2.map (fun x => x + d) f}).Connected := by
  have hinj : Function.Injective (fun x : Fin (m + 3) => x + d) :=
    fun _ _ hxy => add_right_cancel hxy
  have e : ((cycleGraph (m + 3)).deleteEdges {f}) ≃g
      ((cycleGraph (m + 3)).deleteEdges {Sym2.map (fun x => x + d) f}) := by
    refine ⟨Equiv.addRight d, ?_⟩
    intro a b
    simp only [SimpleGraph.deleteEdges_adj, Equiv.coe_addRight, Set.mem_singleton_iff]
    refine and_congr ?_ ?_
    · exact circulantGraph_adj_translate
    · rw [show (s(a + d, b + d) : Sym2 (Fin (m + 3)))
            = Sym2.map (fun x => x + d) s(a, b) from rfl]
      exact (Sym2.map.injective hinj).ne_iff
  exact e.connected_iff.mp h

/-- **Deleting one edge of the cycle keeps it connected**: for any edge `e` of
`cycleGraph (m+3)`, the graph reconstructed from the remaining edges
`fromEdgeSet ↑(edgeFinset.erase e)` is `Connected`.

Proof outline.  First identify `fromEdgeSet ↑(edgeFinset.erase e)` with
`(cycleGraph (m+3)).deleteEdges {e}`.  Writing `e = s(a, a+1)` via the edge
enumeration, the wrap edge `s(0, Fin.last (m+2))` deleted leaves a supergraph of
`pathGraph (m+3)` (the path edges are exactly the non-wrap cycle edges), hence is
connected; the rotation `x ↦ x + (a+1)` (`deleteEdges_translate_connected`)
carries the wrap edge to `e`. -/
private theorem cycleGraph_fromEdgeSet_erase_connected (m : ℕ)
    {e : Sym2 (Fin (m + 3))} (he : e ∈ (cycleGraph (m + 3)).edgeFinset) :
    (SimpleGraph.fromEdgeSet
        (↑((cycleGraph (m + 3)).edgeFinset.erase e) : Set (Sym2 (Fin (m + 3))))).Connected := by
  -- Step 1: `fromEdgeSet ↑(E.erase e) = (cycleGraph (m+3)).deleteEdges {e}`.
  have hstep1 : SimpleGraph.fromEdgeSet
        (↑((cycleGraph (m + 3)).edgeFinset.erase e) : Set (Sym2 (Fin (m + 3))))
      = (cycleGraph (m + 3)).deleteEdges {e} := by
    ext u v
    simp only [SimpleGraph.fromEdgeSet_adj, SimpleGraph.deleteEdges_adj, Finset.coe_erase,
      Set.mem_diff, Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hadj, hne⟩, _⟩
      exact ⟨hadj, hne⟩
    · rintro ⟨hadj, hne⟩
      exact ⟨⟨hadj, hne⟩, hadj.ne⟩
  rw [hstep1]
  -- Write `e = s(a, a+1)` via the edge enumeration.
  have hEimg : (cycleGraph (m + 3)).edgeFinset
      = Finset.image (fun i : Fin (m + 3) => s(i, i + 1)) Finset.univ :=
    TransferMatrix.cycleGraph_edgeFinset_eq_image (m + 1)
  rw [hEimg, Finset.mem_image] at he
  obtain ⟨a, -, rfl⟩ := he
  -- Step 2: deleting the wrap edge `s(0, last)` leaves a supergraph of the path.
  have hle : pathGraph (m + 3) ≤ (cycleGraph (m + 3)).deleteEdges
      ({s((0 : Fin (m + 3)), Fin.last (m + 2))} : Set (Sym2 (Fin (m + 3)))) := by
    intro u v huv
    rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
    refine ⟨pathGraph_le_cycleGraph huv, ?_⟩
    rw [SimpleGraph.pathGraph_adj] at huv
    intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · rw [Fin.val_zero, Fin.val_last] at huv
        omega
  have hwrap : ((cycleGraph (m + 3)).deleteEdges
      ({s((0 : Fin (m + 3)), Fin.last (m + 2))} : Set (Sym2 (Fin (m + 3))))).Connected :=
    (pathGraph_connected (m + 2)).mono hle
  -- Step 3: the rotation `x ↦ x + (a+1)` carries the wrap edge to `s(a, a+1)`.
  have hlast1 : (Fin.last (m + 2) : Fin (m + 3)) + 1 = 0 :=
    neg_eq_iff_add_eq_zero.mp (Fin.neg_last (m + 2))
  have hmap : Sym2.map (fun x => x + (a + 1)) (s((0 : Fin (m + 3)), Fin.last (m + 2)))
      = s(a, a + 1) := by
    rw [Sym2.map_mk,
      show (0 : Fin (m + 3)) + (a + 1) = a + 1 from by rw [zero_add],
      show (Fin.last (m + 2) : Fin (m + 3)) + (a + 1) = a from by
        rw [add_comm a 1, ← add_assoc, hlast1, zero_add]]
    exact Sym2.eq_swap
  have hconn := deleteEdges_translate_connected m (a + 1)
    (s((0 : Fin (m + 3)), Fin.last (m + 2))) hwrap
  rwa [hmap] at hconn

/-- **Characterization of connected spanning edge-subsets of the cycle**: the
connected spanning subsets of `cycleGraph (m+3)` are exactly the full edge set `E`
together with the `m+3` single-edge deletions `E.erase e` (`e ∈ E`).

Forward direction: a connected spanning subgraph on `m+3` vertices needs at least
`m+2` edges (`Connected.card_vert_le_card_edgeSet_add_one`); with `S ⊆ E` and
`|E| = m+3` this forces `|S| ∈ {m+2, m+3}`, i.e. `S = E` or `S = E.erase e`.
Backward direction: `E` is connected (`cycleGraph_connected`) and each `E.erase e`
is connected (`cycleGraph_fromEdgeSet_erase_connected`). -/
private theorem cycleGraph_connectedSpanning_charac (m : ℕ) :
    connectedSpanningEdgeSubsets (cycleGraph (m + 3))
      = insert ((cycleGraph (m + 3)).edgeFinset)
          ((cycleGraph (m + 3)).edgeFinset.image
            (fun e => (cycleGraph (m + 3)).edgeFinset.erase e)) := by
  have hEcard : (cycleGraph (m + 3)).edgeFinset.card = m + 3 :=
    TransferMatrix.card_cycleGraph_edgeFinset m
  have hGE : SimpleGraph.fromEdgeSet
        (↑((cycleGraph (m + 3)).edgeFinset) : Set (Sym2 (Fin (m + 3))))
      = cycleGraph (m + 3) := by
    rw [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet]
  ext S
  rw [mem_connectedSpanningEdgeSubsets, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨hsub, hconn⟩
    -- The edge set of `fromEdgeSet ↑S` is `↑S` (no diagonal edges since `S ⊆ E`).
    have hES : (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin (m + 3))))).edgeSet
        = (↑S : Set (Sym2 (Fin (m + 3)))) := by
      rw [SimpleGraph.edgeSet_fromEdgeSet, sdiff_eq_left, Set.disjoint_left]
      intro x hxS hxdiag
      have hxE : x ∈ (cycleGraph (m + 3)).edgeSet :=
        SimpleGraph.mem_edgeFinset.mp (hsub (Finset.mem_coe.mp hxS))
      have hnd : ¬ x.IsDiag := SimpleGraph.not_isDiag_of_mem_edgeSet _ hxE
      exact hnd (Sym2.mem_diagSet.mp hxdiag)
    -- A connected spanning subgraph has at least `m+2` edges.
    have hSge : m + 2 ≤ S.card := by
      have hc := hconn.card_vert_le_card_edgeSet_add_one
      rw [Nat.card_eq_fintype_card, Fintype.card_fin, hES, Nat.card_coe_set_eq,
        Set.ncard_coe_finset] at hc
      omega
    have hSle : S.card ≤ m + 3 :=
      le_of_le_of_eq (Finset.card_le_card hsub) hEcard
    rcases Nat.lt_or_ge S.card (m + 3) with hlt | hge
    · -- `|S| = m+2`: `S = E.erase e` where `{e} = E \ S`.
      right
      have hScard : S.card = m + 2 := by omega
      have hsdiff : ((cycleGraph (m + 3)).edgeFinset \ S).card = 1 := by
        rw [Finset.card_sdiff_of_subset hsub, hEcard, hScard]; omega
      obtain ⟨e, he_eq⟩ := Finset.card_eq_one.mp hsdiff
      have heE : e ∈ (cycleGraph (m + 3)).edgeFinset := by
        have hmem : e ∈ (cycleGraph (m + 3)).edgeFinset \ S := by
          rw [he_eq]; exact Finset.mem_singleton_self e
        exact (Finset.mem_sdiff.mp hmem).1
      refine ⟨e, heE, ?_⟩
      rw [Finset.erase_eq, ← he_eq, Finset.sdiff_sdiff_self_left,
        Finset.inter_eq_right.mpr hsub]
    · -- `|S| = m+3`: `S = E`.
      left
      exact Finset.eq_of_subset_of_card_le hsub (by rw [hEcard]; exact hge)
  · rintro (rfl | ⟨e, heE, rfl⟩)
    · exact ⟨Finset.Subset.refl _, by rw [hGE]; exact cycleGraph_connected⟩
    · exact ⟨Finset.erase_subset _ _, cycleGraph_fromEdgeSet_erase_connected m heE⟩

/-- **General closed form for the cycle-graph alternating connected-spanning sum**
(Mayer Phase B, Glimm–Jaffe §18.4): for `3 ≤ n`,

  `alternatingConnectedSubgraphSum (cycleGraph n) = (-1)^(n-1) · (n-1)`.

The connected spanning subsets are the full cycle (size `n`) and the `n`
single-edge deletions (size `n-1`), so the alternating sum is
`(-1)^n + n·(-1)^(n-1) = (-1)^(n-1)·(n-1)`.  This subsumes the former per-`n`
`decide` lemmas for `n = 3, …, 7`.  Values: `n=3 ↦ 2`, `4 ↦ -3`, `5 ↦ 4`,
`6 ↦ -5`, `7 ↦ 6`. -/
theorem alternatingConnectedSubgraphSum_cycleGraph (n : ℕ) (hn : 3 ≤ n) :
    alternatingConnectedSubgraphSum (SimpleGraph.cycleGraph n)
      = (-1 : ℝ) ^ (n - 1) * (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hEcard : (cycleGraph (m + 3)).edgeFinset.card = m + 3 :=
    TransferMatrix.card_cycleGraph_edgeFinset m
  have hnotmem : (cycleGraph (m + 3)).edgeFinset ∉
      (cycleGraph (m + 3)).edgeFinset.image
        (fun e => (cycleGraph (m + 3)).edgeFinset.erase e) := by
    rw [Finset.mem_image]
    rintro ⟨e, he, heq⟩
    exact (Finset.notMem_erase e _) (heq ▸ he)
  have hinjOn : Set.InjOn (fun e => (cycleGraph (m + 3)).edgeFinset.erase e)
      ↑(cycleGraph (m + 3)).edgeFinset := by
    intro x hx y _ hxy
    simp only at hxy
    by_contra hne
    have hx' : x ∈ (cycleGraph (m + 3)).edgeFinset.erase y :=
      Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp hx⟩
    rw [← hxy] at hx'
    exact (Finset.notMem_erase x _) hx'
  have hsum2 : ∀ e ∈ (cycleGraph (m + 3)).edgeFinset,
      (-1 : ℝ) ^ ((cycleGraph (m + 3)).edgeFinset.erase e).card = (-1 : ℝ) ^ (m + 2) := by
    intro e he
    rw [Finset.card_erase_of_mem he, hEcard, show m + 3 - 1 = m + 2 from rfl]
  have hpow : (-1 : ℝ) ^ (m + 3) = (-1 : ℝ) ^ (m + 2) * (-1) := by
    rw [show m + 3 = (m + 2) + 1 from rfl, pow_succ]
  rw [show m + 3 - 1 = m + 2 from rfl]
  unfold alternatingConnectedSubgraphSum
  rw [cycleGraph_connectedSpanning_charac m, Finset.sum_insert hnotmem,
    Finset.sum_image hinjOn,
    show (∑ e ∈ (cycleGraph (m + 3)).edgeFinset,
          (-1 : ℝ) ^ ((cycleGraph (m + 3)).edgeFinset.erase e).card)
        = ∑ _e ∈ (cycleGraph (m + 3)).edgeFinset, (-1 : ℝ) ^ (m + 2)
      from Finset.sum_congr rfl hsum2,
    Finset.sum_const, hEcard, nsmul_eq_mul, hpow]
  push_cast
  ring

end IsingModel
