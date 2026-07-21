import IsingModel.ClusterExpansion.HighTempGeneralRegularity
import IsingModel.ClusterExpansion.PathGraphAlternatingSum

/-!
# Cluster expansion path graph alternating sums

Mechanical child split from `ClusterExpansion.lean`.

Every value below is an instance of the general closed form
`alternatingConnectedSubgraphSum_pathGraph`
(`IsingModel/ClusterExpansion/PathGraphAlternatingSum.lean`), which replaced the
former per-`n` `decide +kernel` evaluations.
-/

namespace IsingModel

open Finset

/-! ## §18.4 Mayer Phase B: alternating sums on `pathGraph 3, …, 8`

Companion to the K_n base cases (PRs #1514-#1519). The `pathGraph (n+1)`
on `Fin (n+1)` has `n` edges (between consecutive vertices); its
alternating connected-spanning sum equals `(-1)^n`, matching the
"path-shaped cluster" Ursell-coefficient denominators. -/

/-- **`pathGraph 3` alternating connected-spanning sum = 1**: the
graph has 2 edges; the only connected spanning edge subset is the
full edge set `{s(0,1), s(1,2)}` (both edges needed to connect 3
vertices via the path 0 - 1 - 2). Sum = `(-1)^2 = 1`. Matches the
standard Ursell-coefficient identity for an n=3 path cluster:
`ϕ^T = (alternating sum) / n! = 1/6`. Instance of
`alternatingConnectedSubgraphSum_pathGraph` at `n = 2`. -/
theorem alternatingConnectedSubgraphSum_pathGraph_three :
    alternatingConnectedSubgraphSum (SimpleGraph.pathGraph 3) = 1 := by
  have h := alternatingConnectedSubgraphSum_pathGraph 2
  norm_num at h
  exact h

/-- **`pathGraph 4` alternating connected-spanning sum = -1**: the
graph has 3 edges `{s(0,1), s(1,2), s(2,3)}`; the only connected
spanning edge subset is the full edge set (all 3 edges needed to
connect 4 vertices linearly). Sum = `(-1)^3 = -1`. Ursell coefficient
for n=4 path cluster: `ϕ^T = -1/4! = -1/24`. Instance of
`alternatingConnectedSubgraphSum_pathGraph` at `n = 3`. -/
theorem alternatingConnectedSubgraphSum_pathGraph_four :
    alternatingConnectedSubgraphSum (SimpleGraph.pathGraph 4) = -1 := by
  have h := alternatingConnectedSubgraphSum_pathGraph 3
  norm_num at h
  exact h

/-- **`pathGraph 5` alternating connected-spanning sum = 1**: 4 edges,
only the full path is connected spanning, sum = `(-1)^4 = 1`. Ursell
coefficient for n=5 path cluster: `ϕ^T = 1/5! = 1/120`. Instance of
`alternatingConnectedSubgraphSum_pathGraph` at `n = 4`. -/
theorem alternatingConnectedSubgraphSum_pathGraph_five :
    alternatingConnectedSubgraphSum (SimpleGraph.pathGraph 5) = 1 := by
  have h := alternatingConnectedSubgraphSum_pathGraph 4
  norm_num at h
  exact h

/-- **`pathGraph 7` alternating connected-spanning sum = 1**: 6 edges,
only the full path is connected spanning, sum = `(-1)^6 = 1`. Ursell
coefficient for n=7 path cluster: `ϕ^T = 1/7! = 1/5040`. Instance of
`alternatingConnectedSubgraphSum_pathGraph` at `n = 6`. -/
theorem alternatingConnectedSubgraphSum_pathGraph_seven :
    alternatingConnectedSubgraphSum (SimpleGraph.pathGraph 7) = 1 := by
  have h := alternatingConnectedSubgraphSum_pathGraph 6
  norm_num at h
  exact h

/-- **`pathGraph 6` alternating connected-spanning sum = -1**: 5 edges,
only the full path is connected spanning, sum = `(-1)^5 = -1`. Ursell
coefficient for n=6 path cluster: `ϕ^T = -1/6! = -1/720`. Instance of
`alternatingConnectedSubgraphSum_pathGraph` at `n = 5`. -/
theorem alternatingConnectedSubgraphSum_pathGraph_six :
    alternatingConnectedSubgraphSum (SimpleGraph.pathGraph 6) = -1 := by
  have h := alternatingConnectedSubgraphSum_pathGraph 5
  norm_num at h
  exact h

/-- **`pathGraph 8` alternating connected-spanning sum = -1**: 7 edges,
only the full path is connected spanning, sum = `(-1)^7 = -1`. Ursell
coefficient for n=8 path cluster: `ϕ^T = -1/8! = -1/40320`. Instance of
`alternatingConnectedSubgraphSum_pathGraph` at `n = 7`. -/
theorem alternatingConnectedSubgraphSum_pathGraph_eight :
    alternatingConnectedSubgraphSum (SimpleGraph.pathGraph 8) = -1 := by
  have h := alternatingConnectedSubgraphSum_pathGraph 7
  norm_num at h
  exact h

end IsingModel
