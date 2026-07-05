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

## Abstract polymer gas

The counting engine is purely connectivity-based: it never uses even-ness.  It is
therefore stated over an **abstract polymer set** `𝓟 : Finset (Finset (Sym2 ι))`
whose members satisfy `PolymerGasData` (each polymer is a nonempty edge-connected
subset of `G.edgeFinset`).  The even gas (`allPolymers G`, `evenPolymerGasData`)
and, later, the connected/field gas both instantiate this, so the count and the
per-vertex activity moment bounds are proved once over `𝓟`; the even-gas
statements are recovered verbatim as `𝓟 := allPolymers G` wrappers.

The results are finite-graph bounds in terms of `G.maxDegree`.  They do not by
themselves give a volume-uniform Mayer convergence theorem or the infinite-volume
pressure; that is a later assembly.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~378--386.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §3.7.3, eq.~(3.49).
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Abstract polymer-gas data.**  The hypotheses on an abstract polymer set
`𝓟 : Finset (Finset (Sym2 ι))` that the volume-uniform Kotecky--Preiss counting and
moment core consume: every member is a nonempty edge-connected subset of
`G.edgeFinset`.  The even gas (`allPolymers G`) and the connected/field gas both
instantiate this, so the count and per-vertex activity moment bounds are proved once
over `𝓟`.  The support-cardinality bound (`|supp P| ≤ |P|` for even, `≤ |P| + 1` for
connected) is deliberately *not* part of this bundle: the moment core keeps the
`|supp P|` factor and each gas applies its own (tight) support bound in a wrapper. -/
structure PolymerGasData (G : SimpleGraph ι) [Fintype G.edgeSet]
    (𝓟 : Finset (Finset (Sym2 ι))) : Prop where
  /-- Every polymer of the gas is a subset of the edge set of `G`. -/
  mem_edgeFinset : ∀ P ∈ 𝓟, P ⊆ G.edgeFinset
  /-- Every polymer of the gas is edge-connected. -/
  connected : ∀ P ∈ 𝓟, IsEdgeConnected P
  /-- Every polymer of the gas is nonempty. -/
  nonempty : ∀ P ∈ 𝓟, P.Nonempty

/-- The gas polymers (from `𝓟`) whose support contains the vertex `v`. -/
def rootedGasPolymers (𝓟 : Finset (Finset (Sym2 ι))) (v : ι) :
    Finset (Finset (Sym2 ι)) :=
  𝓟.filter fun P => v ∈ polymerSupport P

/-- The gas polymers (from `𝓟`) of size `ℓ` whose support contains the vertex `v`. -/
def rootedGasPolymersOfCard (𝓟 : Finset (Finset (Sym2 ι))) (v : ι) (ℓ : ℕ) :
    Finset (Finset (Sym2 ι)) :=
  (rootedGasPolymers 𝓟 v).filter fun P => P.card = ℓ

/-- **Rooted gas polymers inject into closed walks.**  The number of size-`ℓ`
polymers of the gas `𝓟` through `v` is at most the number of closed walks of length
`2ℓ` from `v`.  Uses only the connectivity data of `PolymerGasData`. -/
theorem rootedGasPolymersOfCard_card_le_closedWalkCount (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {𝓟 : Finset (Finset (Sym2 ι))}
    (hgas : PolymerGasData G 𝓟) (v : ι) (ℓ : ℕ) :
    (rootedGasPolymersOfCard 𝓟 v ℓ).card ≤ (G.finsetWalkLength (2 * ℓ) v v).card := by
  refine card_connected_edge_sets_le v ℓ _ (fun C hC => ?_)
  rw [rootedGasPolymersOfCard, Finset.mem_filter, rootedGasPolymers, Finset.mem_filter] at hC
  obtain ⟨⟨hCmem, hCv⟩, hCcard⟩ := hC
  exact ⟨hgas.mem_edgeFinset C hCmem, hgas.connected C hCmem, hCcard,
    mem_polymerSupport.mp hCv⟩

/-- **Max-degree bound on rooted gas polymer counts (volume-uniform).**  The number
of size-`ℓ` polymers of the gas `𝓟` through `v` is at most `Δ^{2ℓ}`, where
`Δ = G.maxDegree`. -/
theorem rootedGasPolymersOfCard_card_le_maxDegree_pow (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {𝓟 : Finset (Finset (Sym2 ι))}
    (hgas : PolymerGasData G 𝓟) (v : ι) (ℓ : ℕ) :
    (rootedGasPolymersOfCard 𝓟 v ℓ).card ≤ G.maxDegree ^ (2 * ℓ) := by
  refine (rootedGasPolymersOfCard_card_le_closedWalkCount G hgas v ℓ).trans ?_
  refine le_trans ?_ (walksFromCount_le_pow G (fun w => G.degree_le_maxDegree w) (2 * ℓ) v)
  rw [walksFromCount]
  exact Finset.single_le_sum (f := fun u => (G.finsetWalkLength (2 * ℓ) v u).card)
    (fun u _ => Nat.zero_le _) (Finset.mem_univ v)

omit [Fintype ι] in
/-- **The even gas satisfies the polymer-gas hypotheses.**  Every even-subgraph
polymer of `allPolymers G` is a nonempty edge-connected subset of `G.edgeFinset`. -/
theorem evenPolymerGasData (G : SimpleGraph ι) [Fintype G.edgeSet] :
    PolymerGasData G (allPolymers G) where
  mem_edgeFinset _ hP := (mem_allPolymers.mp hP).isEven.subset
  connected _ hP := (mem_allPolymers.mp hP).connected
  nonempty _ hP := (mem_allPolymers.mp hP).nonempty

/-- The polymers of `G` whose support contains the vertex `v` (even gas). -/
noncomputable def rootedPolymers (G : SimpleGraph ι) [Fintype G.edgeSet] (v : ι) :
    Finset (Finset (Sym2 ι)) :=
  rootedGasPolymers (allPolymers G) v

/-- The polymers of `G` of size `ℓ` whose support contains the vertex `v` (even gas). -/
noncomputable def rootedPolymersOfCard (G : SimpleGraph ι) [Fintype G.edgeSet]
    (v : ι) (ℓ : ℕ) : Finset (Finset (Sym2 ι)) :=
  rootedGasPolymersOfCard (allPolymers G) v ℓ

/-- **Rooted polymers inject into closed walks.**  The number of size-`ℓ` polymers
through `v` is at most the number of closed walks of length `2ℓ` from `v`. -/
theorem rootedPolymersOfCard_card_le_closedWalkCount (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (v : ι) (ℓ : ℕ) :
    (rootedPolymersOfCard G v ℓ).card ≤ (G.finsetWalkLength (2 * ℓ) v v).card :=
  rootedGasPolymersOfCard_card_le_closedWalkCount G (evenPolymerGasData G) v ℓ

/-- **Max-degree bound on rooted polymer counts (volume-uniform).**  The number of
size-`ℓ` polymers through `v` is at most `Δ^{2ℓ}`, where `Δ = G.maxDegree`. -/
theorem rootedPolymersOfCard_card_le_maxDegree_pow (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (v : ι) (ℓ : ℕ) :
    (rootedPolymersOfCard G v ℓ).card ≤ G.maxDegree ^ (2 * ℓ) :=
  rootedGasPolymersOfCard_card_le_maxDegree_pow G (evenPolymerGasData G) v ℓ

end IsingModel
