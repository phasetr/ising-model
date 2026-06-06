import IsingModel.Conditioning.WalkCountDegreeBound

/-!
# Counting closed walks in the box lattice (FV §3.7.2)

The number of closed walks of length `k` from a fixed vertex `v` in the induced box graph is
bounded by `(2d)^k`: closed walks are among all walks from `v`, whose total count
(`walksFromCount`) is at most `(2d)^k` by the degree bound. This is the counting engine for the
Peierls contour bound — a dart orbit of length `k` is a closed walk, so the number of contours of
a given length near a fixed vertex is geometric in the length.

* `closedWalkCount_le` — `#{closed walks of length k from v} ≤ (2d)^k`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **Closed walks are geometrically bounded**: the number of closed walks of length `k` from a
vertex `v` in the induced box graph `inducedGraph (latticeGraph d) Λ` is at most `(2d)^k`. -/
theorem closedWalkCount_le {d : ℕ} (Λ : Finset (Fin d → ℤ)) (v : ↑Λ) (k : ℕ) :
    ((Ambient.inducedGraph (latticeGraph d) Λ).finsetWalkLength k v v).card ≤ (2 * d) ^ k := by
  have hsum : ((Ambient.inducedGraph (latticeGraph d) Λ).finsetWalkLength k v v).card ≤
      walksFromCount (Ambient.inducedGraph (latticeGraph d) Λ) v k := by
    unfold walksFromCount
    exact Finset.single_le_sum
      (f := fun w => ((Ambient.inducedGraph (latticeGraph d) Λ).finsetWalkLength k v w).card)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ v)
  exact hsum.trans (walksFromCount_inducedLatticeGraph_le Λ v k)

end IsingModel
