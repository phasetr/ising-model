import IsingModel.ClusterExpansion.Families.EvenSubgraphs
import IsingModel.Conditioning.EdgeWalkCounting
import IsingModel.Conditioning.WalkCountDegreeBound

/-!
# Rooted polymer counting and the per-vertex activity bound (GJ §18.5)

The volume-uniform input to the Kotecky--Preiss cluster-expansion criterion is a
bound on the polymer activity *through a fixed vertex* that depends only on the
maximum degree, not on the volume.  Polymers are connected edge sets, so the
rooted polymers of size `ℓ` through `v` inject (FV §3.7.3, via
`card_connected_edge_sets_le`) into the closed walks of length `2ℓ` from `v`,
whose number is at most `Δ^{2ℓ}` (`walksFromCount_le_pow`).  Summing the geometric
series gives a per-vertex activity bound
`∑_{P ∋ v} t^{|P|} ≤ (1 − Δ²t)⁻¹` under `Δ²t < 1` — uniform in the volume.

This is the first reusable volume-uniform object for the §18.5 infinite-volume
cluster expansion; the (per-volume) high-temperature conditions of
`InteractingFreeEnergyMayerHighTemp` grow with the volume, whereas this bound does
not.

The results are finite-graph bounds in terms of `G.maxDegree`.  They do not by
themselves give a volume-uniform Mayer convergence theorem or the infinite-volume
pressure; that is a later assembly.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~378--386.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §3.7.3, eq.~(3.49).
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The polymers of `G` whose support contains the vertex `v`. -/
noncomputable def rootedPolymers (G : SimpleGraph ι) [Fintype G.edgeSet] (v : ι) :
    Finset (Finset (Sym2 ι)) :=
  (allPolymers G).filter fun P => v ∈ polymerSupport P

/-- The polymers of `G` of size `ℓ` whose support contains the vertex `v`. -/
noncomputable def rootedPolymersOfCard (G : SimpleGraph ι) [Fintype G.edgeSet]
    (v : ι) (ℓ : ℕ) : Finset (Finset (Sym2 ι)) :=
  (rootedPolymers G v).filter fun P => P.card = ℓ

/-- **Rooted polymers inject into closed walks.**  The number of size-`ℓ` polymers
through `v` is at most the number of closed walks of length `2ℓ` from `v`. -/
theorem rootedPolymersOfCard_card_le_closedWalkCount (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (v : ι) (ℓ : ℕ) :
    (rootedPolymersOfCard G v ℓ).card ≤ (G.finsetWalkLength (2 * ℓ) v v).card := by
  refine card_connected_edge_sets_le v ℓ _ (fun C hC => ?_)
  rw [rootedPolymersOfCard, Finset.mem_filter, rootedPolymers, Finset.mem_filter] at hC
  obtain ⟨⟨hCmem, hCv⟩, hCcard⟩ := hC
  have hpoly : IsPolymer G C := mem_allPolymers.mp hCmem
  exact ⟨hpoly.isEven.subset, hpoly.connected, hCcard, mem_polymerSupport.mp hCv⟩

/-- **Max-degree bound on rooted polymer counts (volume-uniform).**  The number of
size-`ℓ` polymers through `v` is at most `Δ^{2ℓ}`, where `Δ = G.maxDegree`. -/
theorem rootedPolymersOfCard_card_le_maxDegree_pow (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (v : ι) (ℓ : ℕ) :
    (rootedPolymersOfCard G v ℓ).card ≤ G.maxDegree ^ (2 * ℓ) := by
  refine (rootedPolymersOfCard_card_le_closedWalkCount G v ℓ).trans ?_
  refine le_trans ?_ (walksFromCount_le_pow G (fun w => G.degree_le_maxDegree w) (2 * ℓ) v)
  rw [walksFromCount]
  exact Finset.single_le_sum (f := fun u => (G.finsetWalkLength (2 * ℓ) v u).card)
    (fun u _ => Nat.zero_le _) (Finset.mem_univ v)

end IsingModel
