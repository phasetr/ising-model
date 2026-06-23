import IsingModel.ClusterExpansion.TwoPointNumeratorBound
import IsingModel.ClusterExpansion.PolymerCounting

/-!
# Anchored count of two-point connecting components (GJ §18.4–18.7, FV §3.7.3)

Volume-uniform combinatorial input to the two-point bound `hbdd` (Issue #4230, item D of #4214).
The outer sum of the brick-4 numerator bound (`htSubgraphSum_pair_norm_le`) ranges over
`connectingComponents G i j` — the nonempty edge-connected `C ⊆ G.edgeFinset` with `∂C = {i,j}`.
To turn that sum into a convergent geometric series (via `sum_le_geometric_of_fiber_card_le`), one
needs a volume-uniform bound on the number of such components of a fixed size `ℓ`.

Every connecting component is a connected edge subset of size `ℓ` whose support contains `i` (since
`i ∈ ∂C ⊆ polymerSupport C`, `oddBoundary_subset_polymerSupport`).  Such anchored connected edge
sets inject into the closed walks of length `2ℓ` from `i` (`card_connected_edge_sets_le`, FV §3.7.3,
via the spanning-walk encoding — evenness is *not* used, only connectivity), whose number is at most
`Δ^{2ℓ}` (`walksFromCount_le_pow`).  This mirrors `rootedPolymersOfCard_card_le_maxDegree_pow` for
polymers, dropping the evenness requirement.

## Main result
* `connectingComponentsOfCard_card_le_maxDegree_pow` — `|{C ∈ connectingComponents G i j : |C| = ℓ}|
  ≤ Δ^{2ℓ}`, volume-uniform.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §18.4–18.7; Friedli–Velenik,
*Statistical Mechanics of Lattice Systems* (CUP, 2017), §3.7.3.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Volume-uniform anchored count of two-point connecting components.**  The number of
connecting components `C` (edge-connected, `∂C = {i,j}`) of size `ℓ` is at most `Δ^{2ℓ}`, where
`Δ = G.maxDegree` — independent of the volume.  Each such `C` is a connected edge subset of size `ℓ`
through `i`, so it injects into the closed walks of length `2ℓ` from `i`. -/
theorem connectingComponentsOfCard_card_le_maxDegree_pow (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (i j : ι) (ℓ : ℕ) :
    ((connectingComponents G i j).filter (fun C => C.card = ℓ)).card
      ≤ G.maxDegree ^ (2 * ℓ) := by
  classical
  refine le_trans (card_connected_edge_sets_le (G := G) i ℓ _ (fun C hC => ?_)) ?_
  · simp only [Finset.mem_filter, connectingComponents, Finset.mem_powerset] at hC
    obtain ⟨⟨hCsub, _hCne, hCconn, hCbd⟩, hCcard⟩ := hC
    refine ⟨hCsub, hCconn, hCcard, ?_⟩
    have hi : i ∈ polymerSupport C := by
      apply oddBoundary_subset_polymerSupport C
      rw [hCbd]; simp
    exact mem_polymerSupport.mp hi
  · refine le_trans ?_ (walksFromCount_le_pow G (fun w => G.degree_le_maxDegree w) (2 * ℓ) i)
    rw [walksFromCount]
    exact Finset.single_le_sum (f := fun u => (G.finsetWalkLength (2 * ℓ) i u).card)
      (fun u _ => Nat.zero_le _) (Finset.mem_univ i)

end IsingModel
