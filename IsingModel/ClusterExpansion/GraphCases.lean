import IsingModel.ClusterExpansion.HighTempGeneralRegularity
import IsingModel.ClusterExpansion.CycleGraphAlternatingSum

/-!
# Cluster expansion path and cycle graph alternating sums

Mechanical child split from `ClusterExpansion.lean`.
-/

namespace IsingModel

open Finset

/-! ## §18.4 Mayer Phase B: alternating sum on `pathGraph 3`

Companion to the K_n base cases (PRs #1514-#1519). The `pathGraph 3`
on `Fin 3` has 2 edges (between consecutive vertices); its
alternating connected-spanning sum equals 1, matching the n=3
"path-shaped cluster" Ursell-coefficient denominator. -/

/-- **Path graph on `Fin 3` `DecidableRel` instance**: needed for
`Fintype` of the edge set + `decide`-based proofs. -/
private instance : DecidableRel (SimpleGraph.pathGraph 3).Adj :=
  fun _ _ => decidable_of_iff _ SimpleGraph.pathGraph_adj.symm

/-- **Path graph on `Fin 3` edge finset** = `{s(0,1), s(1,2)}`. -/
private theorem pathGraph_three_edgeFinset :
    (SimpleGraph.pathGraph 3).edgeFinset = {s(0, 1), s(1, 2)} := by
  classical
  apply Finset.ext
  intro e
  rw [SimpleGraph.mem_edgeFinset]
  refine ⟨?_, fun h => ?_⟩
  · induction e using Sym2.ind with
    | h a b =>
      intro hab
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.pathGraph_adj] at hab
      fin_cases a <;> fin_cases b <;> simp_all [Sym2.eq_swap]
  · rcases (by simpa using h : e = s(0,1) ∨ e = s(1,2)) with h | h <;>
      · subst h
        rw [SimpleGraph.mem_edgeSet, SimpleGraph.pathGraph_adj]
        decide

/-- **`pathGraph 3` alternating connected-spanning sum = 1**: the
graph has 2 edges; the only connected spanning edge subset is the
full edge set `{s(0,1), s(1,2)}` (both edges needed to connect 3
vertices via the path 0 - 1 - 2). Sum = `(-1)^2 = 1`. Matches the
standard Ursell-coefficient identity for an n=3 path cluster:
`ϕ^T = (alternating sum) / n! = 1/6`. -/
theorem alternatingConnectedSubgraphSum_pathGraph_three :
    alternatingConnectedSubgraphSum (SimpleGraph.pathGraph 3) = 1 := by
  classical
  unfold alternatingConnectedSubgraphSum
  -- Convert to integer-valued sum then `decide`.
  have h_int :
      (∑ S ∈ (SimpleGraph.pathGraph 3).edgeFinset.powerset.filter
        (fun S : Finset (Sym2 (Fin 3)) =>
          (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 3)))).Connected),
        ((-1 : ℤ) ^ S.card)) = 1 := by decide
  unfold connectedSpanningEdgeSubsets
  have h_cast :
      (∑ S ∈ (SimpleGraph.pathGraph 3).edgeFinset.powerset.filter
          (fun S : Finset (Sym2 (Fin 3)) =>
            (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 3)))).Connected),
        ((-1 : ℝ) ^ S.card)) =
        (((∑ S ∈ (SimpleGraph.pathGraph 3).edgeFinset.powerset.filter
            (fun S : Finset (Sym2 (Fin 3)) =>
              (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 3)))).Connected),
          ((-1 : ℤ) ^ S.card)) : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [h_cast, h_int]
  norm_num

/-- **Path graph on `Fin 4` `DecidableRel` instance**. -/
private instance : DecidableRel (SimpleGraph.pathGraph 4).Adj :=
  fun _ _ => decidable_of_iff _ SimpleGraph.pathGraph_adj.symm

/-- **`pathGraph 4` alternating connected-spanning sum = -1**: the
graph has 3 edges `{s(0,1), s(1,2), s(2,3)}`; the only connected
spanning edge subset is the full edge set (all 3 edges needed to
connect 4 vertices linearly). Sum = `(-1)^3 = -1`. Ursell coefficient
for n=4 path cluster: `ϕ^T = -1/4! = -1/24`. -/
theorem alternatingConnectedSubgraphSum_pathGraph_four :
    alternatingConnectedSubgraphSum (SimpleGraph.pathGraph 4) = -1 := by
  classical
  unfold alternatingConnectedSubgraphSum
  have h_int :
      (∑ S ∈ (SimpleGraph.pathGraph 4).edgeFinset.powerset.filter
        (fun S : Finset (Sym2 (Fin 4)) =>
          (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 4)))).Connected),
        ((-1 : ℤ) ^ S.card)) = -1 := by decide
  unfold connectedSpanningEdgeSubsets
  have h_cast :
      (∑ S ∈ (SimpleGraph.pathGraph 4).edgeFinset.powerset.filter
          (fun S : Finset (Sym2 (Fin 4)) =>
            (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 4)))).Connected),
        ((-1 : ℝ) ^ S.card)) =
        (((∑ S ∈ (SimpleGraph.pathGraph 4).edgeFinset.powerset.filter
            (fun S : Finset (Sym2 (Fin 4)) =>
              (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 4)))).Connected),
          ((-1 : ℤ) ^ S.card)) : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [h_cast, h_int]
  norm_num

/-- **Path graph on `Fin 5` `DecidableRel` instance**. -/
private instance : DecidableRel (SimpleGraph.pathGraph 5).Adj :=
  fun _ _ => decidable_of_iff _ SimpleGraph.pathGraph_adj.symm

/-- **`pathGraph 5` alternating connected-spanning sum = 1**: 4 edges,
only the full path is connected spanning, sum = `(-1)^4 = 1`. Ursell
coefficient for n=5 path cluster: `ϕ^T = 1/5! = 1/120`. -/
theorem alternatingConnectedSubgraphSum_pathGraph_five :
    alternatingConnectedSubgraphSum (SimpleGraph.pathGraph 5) = 1 := by
  classical
  unfold alternatingConnectedSubgraphSum
  have h_int :
      (∑ S ∈ (SimpleGraph.pathGraph 5).edgeFinset.powerset.filter
        (fun S : Finset (Sym2 (Fin 5)) =>
          (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 5)))).Connected),
        ((-1 : ℤ) ^ S.card)) = 1 := by decide
  unfold connectedSpanningEdgeSubsets
  have h_cast :
      (∑ S ∈ (SimpleGraph.pathGraph 5).edgeFinset.powerset.filter
          (fun S : Finset (Sym2 (Fin 5)) =>
            (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 5)))).Connected),
        ((-1 : ℝ) ^ S.card)) =
        (((∑ S ∈ (SimpleGraph.pathGraph 5).edgeFinset.powerset.filter
            (fun S : Finset (Sym2 (Fin 5)) =>
              (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 5)))).Connected),
          ((-1 : ℤ) ^ S.card)) : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [h_cast, h_int]
  norm_num

/-- **Path graph on `Fin 6` `DecidableRel` instance**. -/
private instance : DecidableRel (SimpleGraph.pathGraph 6).Adj :=
  fun _ _ => decidable_of_iff _ SimpleGraph.pathGraph_adj.symm

/-- **Path graph on `Fin 7` `DecidableRel` instance**. -/
private instance : DecidableRel (SimpleGraph.pathGraph 7).Adj :=
  fun _ _ => decidable_of_iff _ SimpleGraph.pathGraph_adj.symm

set_option maxRecDepth 4000 in
/-- **`pathGraph 7` alternating connected-spanning sum = 1**: 6 edges,
only the full path is connected spanning, sum = `(-1)^6 = 1`. Ursell
coefficient for n=7 path cluster: `ϕ^T = 1/7! = 1/5040`. -/
theorem alternatingConnectedSubgraphSum_pathGraph_seven :
    alternatingConnectedSubgraphSum (SimpleGraph.pathGraph 7) = 1 := by
  classical
  unfold alternatingConnectedSubgraphSum
  have h_int :
      (∑ S ∈ (SimpleGraph.pathGraph 7).edgeFinset.powerset.filter
        (fun S : Finset (Sym2 (Fin 7)) =>
          (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 7)))).Connected),
        ((-1 : ℤ) ^ S.card)) = 1 := by decide
  unfold connectedSpanningEdgeSubsets
  have h_cast :
      (∑ S ∈ (SimpleGraph.pathGraph 7).edgeFinset.powerset.filter
          (fun S : Finset (Sym2 (Fin 7)) =>
            (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 7)))).Connected),
        ((-1 : ℝ) ^ S.card)) =
        (((∑ S ∈ (SimpleGraph.pathGraph 7).edgeFinset.powerset.filter
            (fun S : Finset (Sym2 (Fin 7)) =>
              (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 7)))).Connected),
          ((-1 : ℤ) ^ S.card)) : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [h_cast, h_int]
  norm_num

set_option maxRecDepth 2000 in
/-- **`pathGraph 6` alternating connected-spanning sum = -1**: 5 edges,
only the full path is connected spanning, sum = `(-1)^5 = -1`. Ursell
coefficient for n=6 path cluster: `ϕ^T = -1/6! = -1/720`. -/
theorem alternatingConnectedSubgraphSum_pathGraph_six :
    alternatingConnectedSubgraphSum (SimpleGraph.pathGraph 6) = -1 := by
  classical
  unfold alternatingConnectedSubgraphSum
  have h_int :
      (∑ S ∈ (SimpleGraph.pathGraph 6).edgeFinset.powerset.filter
        (fun S : Finset (Sym2 (Fin 6)) =>
          (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 6)))).Connected),
        ((-1 : ℤ) ^ S.card)) = -1 := by decide
  unfold connectedSpanningEdgeSubsets
  have h_cast :
      (∑ S ∈ (SimpleGraph.pathGraph 6).edgeFinset.powerset.filter
          (fun S : Finset (Sym2 (Fin 6)) =>
            (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 6)))).Connected),
        ((-1 : ℝ) ^ S.card)) =
        (((∑ S ∈ (SimpleGraph.pathGraph 6).edgeFinset.powerset.filter
            (fun S : Finset (Sym2 (Fin 6)) =>
              (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 6)))).Connected),
          ((-1 : ℤ) ^ S.card)) : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [h_cast, h_int]
  norm_num

/-- **Path graph on `Fin 8` `DecidableRel` instance**. -/
private instance : DecidableRel (SimpleGraph.pathGraph 8).Adj :=
  fun _ _ => decidable_of_iff _ SimpleGraph.pathGraph_adj.symm

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
-- `decide` on `pathGraph 8` (7 edges, 2^7 = 128 subsets) needs the
-- raised recursion / heartbeat limits; the default budget runs out
-- mid-decision while enumerating connected spanning edge subsets.
/-- **`pathGraph 8` alternating connected-spanning sum = -1**: 7 edges,
only the full path is connected spanning, sum = `(-1)^7 = -1`. Ursell
coefficient for n=8 path cluster: `ϕ^T = -1/8! = -1/40320`. -/
theorem alternatingConnectedSubgraphSum_pathGraph_eight :
    alternatingConnectedSubgraphSum (SimpleGraph.pathGraph 8) = -1 := by
  classical
  unfold alternatingConnectedSubgraphSum
  have h_int :
      (∑ S ∈ (SimpleGraph.pathGraph 8).edgeFinset.powerset.filter
        (fun S : Finset (Sym2 (Fin 8)) =>
          (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 8)))).Connected),
        ((-1 : ℤ) ^ S.card)) = -1 := by decide
  unfold connectedSpanningEdgeSubsets
  have h_cast :
      (∑ S ∈ (SimpleGraph.pathGraph 8).edgeFinset.powerset.filter
          (fun S : Finset (Sym2 (Fin 8)) =>
            (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 8)))).Connected),
        ((-1 : ℝ) ^ S.card)) =
        (((∑ S ∈ (SimpleGraph.pathGraph 8).edgeFinset.powerset.filter
            (fun S : Finset (Sym2 (Fin 8)) =>
              (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 8)))).Connected),
          ((-1 : ℤ) ^ S.card)) : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [h_cast, h_int]
  norm_num

/-! ## Mayer Phase B: cycleGraph base cases (Issue #1499)

Companion to the K_n and pathGraph cases. The cycleGraph has more
edges than the path on the same vertex set, giving multiple connected
spanning subgraphs (the full cycle plus its spanning trees of size n-1). -/

/-- **`cycleGraph 3` alternating connected-spanning sum = 2** (Mayer Phase B
base case): instance of the general closed form
`alternatingConnectedSubgraphSum_cycleGraph` at `n = 3`,
`(-1)^(3-1)·(3-1) = 2`. Same as `alternatingConnectedSubgraphSum_K3` since
`cycleGraph 3` has the same edge structure as the complete graph `K_3`. -/
theorem alternatingConnectedSubgraphSum_cycleGraph_three :
    alternatingConnectedSubgraphSum (SimpleGraph.cycleGraph 3) = 2 := by
  have h := alternatingConnectedSubgraphSum_cycleGraph 3 (by norm_num)
  norm_num at h
  exact h

/-- **`cycleGraph 4` alternating connected-spanning sum = -3** (Mayer Phase B
base case): instance of the general closed form
`alternatingConnectedSubgraphSum_cycleGraph` at `n = 4`,
`(-1)^(4-1)·(4-1) = -3`. -/
theorem alternatingConnectedSubgraphSum_cycleGraph_four :
    alternatingConnectedSubgraphSum (SimpleGraph.cycleGraph 4) = -3 := by
  have h := alternatingConnectedSubgraphSum_cycleGraph 4 (by norm_num)
  norm_num at h
  exact h

/-- **`cycleGraph 6` alternating connected-spanning sum = -5** (Mayer Phase B
base case): instance of the general closed form
`alternatingConnectedSubgraphSum_cycleGraph` at `n = 6`,
`(-1)^(6-1)·(6-1) = -5`. -/
theorem alternatingConnectedSubgraphSum_cycleGraph_six :
    alternatingConnectedSubgraphSum (SimpleGraph.cycleGraph 6) = -5 := by
  have h := alternatingConnectedSubgraphSum_cycleGraph 6 (by norm_num)
  norm_num at h
  exact h

/-- **`cycleGraph 5` alternating connected-spanning sum = 4** (Mayer Phase B
base case): instance of the general closed form
`alternatingConnectedSubgraphSum_cycleGraph` at `n = 5`,
`(-1)^(5-1)·(5-1) = 4`. -/
theorem alternatingConnectedSubgraphSum_cycleGraph_five :
    alternatingConnectedSubgraphSum (SimpleGraph.cycleGraph 5) = 4 := by
  have h := alternatingConnectedSubgraphSum_cycleGraph 5 (by norm_num)
  norm_num at h
  exact h


end IsingModel
