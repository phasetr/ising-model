import IsingModel.ClusterExpansion.HighTempGeneralRegularity

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

/-- **Cycle graph on `Fin 3` `DecidableRel` instance**. -/
private instance : DecidableRel (SimpleGraph.cycleGraph 3).Adj :=
  fun _ _ => decidable_of_iff _ SimpleGraph.cycleGraph_adj'.symm

/-- **`cycleGraph 3` alternating connected-spanning sum = 2**:
the cycle on Fin 3 has 3 edges (the triangle). Connected spanning
subsets: 3 paths (size 2 each, remove any one edge) + the full
triangle (size 3). Sum = `3 · (-1)^2 + (-1)^3 = 2`. Same as
`alternatingConnectedSubgraphSum_K3` (PR #1518) since `cycleGraph 3`
has the same edge structure as the complete graph K_3. -/
theorem alternatingConnectedSubgraphSum_cycleGraph_three :
    alternatingConnectedSubgraphSum (SimpleGraph.cycleGraph 3) = 2 := by
  classical
  unfold alternatingConnectedSubgraphSum
  have h_int :
      (∑ S ∈ (SimpleGraph.cycleGraph 3).edgeFinset.powerset.filter
        (fun S : Finset (Sym2 (Fin 3)) =>
          (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 3)))).Connected),
        ((-1 : ℤ) ^ S.card)) = 2 := by decide
  unfold connectedSpanningEdgeSubsets
  have h_cast :
      (∑ S ∈ (SimpleGraph.cycleGraph 3).edgeFinset.powerset.filter
          (fun S : Finset (Sym2 (Fin 3)) =>
            (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 3)))).Connected),
        ((-1 : ℝ) ^ S.card)) =
        (((∑ S ∈ (SimpleGraph.cycleGraph 3).edgeFinset.powerset.filter
            (fun S : Finset (Sym2 (Fin 3)) =>
              (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 3)))).Connected),
          ((-1 : ℤ) ^ S.card)) : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [h_cast, h_int]
  norm_num

/-- **Cycle graph on `Fin 4` `DecidableRel` instance**. -/
private instance : DecidableRel (SimpleGraph.cycleGraph 4).Adj :=
  fun _ _ => decidable_of_iff _ SimpleGraph.cycleGraph_adj'.symm

/-- **`cycleGraph 4` alternating connected-spanning sum = -3**:
the cycle on Fin 4 has 4 edges. Connected spanning subsets: 4 paths
(size 3 each, remove any one edge) + the full cycle (size 4).
Sum = `4 · (-1)^3 + (-1)^4 = -4 + 1 = -3`. Distinct from K_4 case
(PR #1519, value -6) since cycleGraph 4 has fewer connected spanning
subsets than K_4 (the K_4 cases include subgraphs containing both
diagonals). -/
theorem alternatingConnectedSubgraphSum_cycleGraph_four :
    alternatingConnectedSubgraphSum (SimpleGraph.cycleGraph 4) = -3 := by
  classical
  unfold alternatingConnectedSubgraphSum
  have h_int :
      (∑ S ∈ (SimpleGraph.cycleGraph 4).edgeFinset.powerset.filter
        (fun S : Finset (Sym2 (Fin 4)) =>
          (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 4)))).Connected),
        ((-1 : ℤ) ^ S.card)) = -3 := by decide
  unfold connectedSpanningEdgeSubsets
  have h_cast :
      (∑ S ∈ (SimpleGraph.cycleGraph 4).edgeFinset.powerset.filter
          (fun S : Finset (Sym2 (Fin 4)) =>
            (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 4)))).Connected),
        ((-1 : ℝ) ^ S.card)) =
        (((∑ S ∈ (SimpleGraph.cycleGraph 4).edgeFinset.powerset.filter
            (fun S : Finset (Sym2 (Fin 4)) =>
              (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 4)))).Connected),
          ((-1 : ℤ) ^ S.card)) : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [h_cast, h_int]
  norm_num

/-- **Cycle graph on `Fin 5` `DecidableRel` instance**. -/
private instance : DecidableRel (SimpleGraph.cycleGraph 5).Adj :=
  fun _ _ => decidable_of_iff _ SimpleGraph.cycleGraph_adj'.symm

/-- **Cycle graph on `Fin 6` `DecidableRel` instance**. -/
private instance : DecidableRel (SimpleGraph.cycleGraph 6).Adj :=
  fun _ _ => decidable_of_iff _ SimpleGraph.cycleGraph_adj'.symm

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
-- `decide` on `cycleGraph 6` (6 edges, 2^6 = 64 subsets) requires the
-- raised recursion / heartbeat budgets to enumerate spanning subsets.
/-- **`cycleGraph 6` alternating connected-spanning sum = -5**:
the cycle on Fin 6 has 6 edges. Connected spanning subsets: 6
spanning trees (paths of size 5 each) + the full cycle (size 6).
Sum = `6 · (-1)^5 + (-1)^6 = -6 + 1 = -5`. -/
theorem alternatingConnectedSubgraphSum_cycleGraph_six :
    alternatingConnectedSubgraphSum (SimpleGraph.cycleGraph 6) = -5 := by
  classical
  unfold alternatingConnectedSubgraphSum
  have h_int :
      (∑ S ∈ (SimpleGraph.cycleGraph 6).edgeFinset.powerset.filter
        (fun S : Finset (Sym2 (Fin 6)) =>
          (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 6)))).Connected),
        ((-1 : ℤ) ^ S.card)) = -5 := by decide
  unfold connectedSpanningEdgeSubsets
  have h_cast :
      (∑ S ∈ (SimpleGraph.cycleGraph 6).edgeFinset.powerset.filter
          (fun S : Finset (Sym2 (Fin 6)) =>
            (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 6)))).Connected),
        ((-1 : ℝ) ^ S.card)) =
        (((∑ S ∈ (SimpleGraph.cycleGraph 6).edgeFinset.powerset.filter
            (fun S : Finset (Sym2 (Fin 6)) =>
              (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 6)))).Connected),
          ((-1 : ℤ) ^ S.card)) : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [h_cast, h_int]
  norm_num

set_option maxRecDepth 4000 in
/-- **`cycleGraph 5` alternating connected-spanning sum = 4**:
the cycle on Fin 5 has 5 edges. Connected spanning subsets: 5
spanning trees (paths of size 4 each) + the full cycle (size 5).
Sum = `5 · (-1)^4 + (-1)^5 = 5 - 1 = 4`. -/
theorem alternatingConnectedSubgraphSum_cycleGraph_five :
    alternatingConnectedSubgraphSum (SimpleGraph.cycleGraph 5) = 4 := by
  classical
  unfold alternatingConnectedSubgraphSum
  have h_int :
      (∑ S ∈ (SimpleGraph.cycleGraph 5).edgeFinset.powerset.filter
        (fun S : Finset (Sym2 (Fin 5)) =>
          (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 5)))).Connected),
        ((-1 : ℤ) ^ S.card)) = 4 := by decide
  unfold connectedSpanningEdgeSubsets
  have h_cast :
      (∑ S ∈ (SimpleGraph.cycleGraph 5).edgeFinset.powerset.filter
          (fun S : Finset (Sym2 (Fin 5)) =>
            (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 5)))).Connected),
        ((-1 : ℝ) ^ S.card)) =
        (((∑ S ∈ (SimpleGraph.cycleGraph 5).edgeFinset.powerset.filter
            (fun S : Finset (Sym2 (Fin 5)) =>
              (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin 5)))).Connected),
          ((-1 : ℤ) ^ S.card)) : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [h_cast, h_int]
  norm_num


end IsingModel
