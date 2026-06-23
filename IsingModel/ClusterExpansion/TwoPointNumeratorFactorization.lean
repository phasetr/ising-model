import IsingModel.ClusterExpansion.SourceGeneratingFunction
import IsingModel.ClusterExpansion.Families.CompatibleProperties

/-!
# Unique connecting component of a two-point subgraph (GJ §18.4–18.7, FV §3.7)

Third brick of the **source-derivative / random-line route** to a volume-uniform bound on the
complex two-point correlation (Issue #4230, item D of #4214; the remaining Ising input `hbdd`).

The high-temperature two-point numerator is `Q_{i,j}(t) = htSubgraphSum G {i,j} t =
∑_{X : ∂X = {i,j}} t^{|X|}` (`SourceGeneratingFunction.lean`).  The volume-uniform bound on the
ratio `Q_{i,j}/Q_∅` rests on the **random-line / connecting-cluster** structure of these subgraphs:
every edge subset `X` with odd-degree boundary `∂X = {i,j}` has **exactly one** connected component
`C` (in the canonical connected-component decomposition `polymerDecomposition X`) whose own boundary
is the whole pair `∂C = {i,j}` — the *open polymer* linking `i` to `j` — while every other component
is an even subgraph (`∂ = ∅`) vertex-disjoint from `C`.  This is the discrete analogue of the unique
*open cluster* connecting the two sources in the high-temperature expansion (the component `C` may
itself contain cycles or several `i`–`j` paths; what is unique is the *component*, not a single
line) (Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §3.7.3; Glimm–Jaffe,
*Quantum Physics*, §18.4–18.7).

The key combinatorial input is that the **odd boundary distributes over the connected-component
decomposition**: `∂X = ⊔_{C ∈ polymerDecomposition X} ∂C`
(`oddBoundary_biUnion_polymerDecomposition`), because the components are pairwise vertex-disjoint,
so all `X`-edges incident to a vertex lie in a single component (`degree_eq_degree_component`).
Combined with the handshake parity
(`oddBoundary_card_even`), a component meeting `{i,j}` must carry the whole pair as its boundary.

## Main results
* `oddBoundary_subset_polymerSupport` — odd-boundary vertices are incident to some edge.
* `oddBoundary_biUnion_polymerDecomposition` — `∂X` distributes over the component decomposition.
* `existsUnique_component_oddBoundary_pair` — the unique connecting component with boundary `{i,j}`.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §18.4–18.7; Friedli–Velenik,
*Statistical Mechanics of Lattice Systems* (CUP, 2017), §3.7.3.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Odd-boundary vertices are supported by the edge set**: every `v ∈ ∂X` is incident to some edge
of `X` (an odd, hence nonzero, incident-edge count). -/
theorem oddBoundary_subset_polymerSupport (X : Finset (Sym2 ι)) :
    oddBoundary X ⊆ polymerSupport X := by
  classical
  intro v hv
  rw [oddBoundary, Finset.mem_filter] at hv
  rw [mem_polymerSupport]
  have hpos : 0 < (X.filter (v ∈ ·)).card := by
    rcases hv.2 with ⟨k, hk⟩
    rw [hk]
    omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at he
  exact ⟨e, he.1, he.2⟩

omit [Fintype ι] in
/-- **A component absorbs all incident edges**: if a component `edgeComponent X e` contains an edge
`f` incident to `v`, it contains *every* `X`-edge incident to `v` (vertex-disjointness of
components), so the incident-edge filters agree. -/
theorem edgeComponent_filter_eq_of_incident
    {X : Finset (Sym2 ι)} {e f : Sym2 ι} {v : ι}
    (hf : f ∈ edgeComponent X e) (hvf : v ∈ f) :
    (edgeComponent X e).filter (v ∈ ·) = X.filter (v ∈ ·) := by
  classical
  apply Finset.Subset.antisymm
  · intro g hg
    rw [Finset.mem_filter] at hg ⊢
    exact ⟨(edgeComponent_subset X e) hg.1, hg.2⟩
  · intro g hg
    rw [Finset.mem_filter] at hg ⊢
    exact ⟨edgeComponent_absorbs_incident hf hvf hg.1 hg.2, hg.2⟩

omit [Fintype ι] in
/-- **Incident-degree localizes to a component**: the incident-edge filter at `v` in `X` equals the
incident-edge filter at `v` inside any component `edgeComponent X e₀` holding an incident edge. -/
theorem degree_eq_degree_component
    {X : Finset (Sym2 ι)} {v : ι} {e₀ : Sym2 ι}
    (he₀ : e₀ ∈ X) (hv₀ : v ∈ e₀) :
    X.filter (v ∈ ·) = (edgeComponent X e₀).filter (v ∈ ·) := by
  exact (edgeComponent_filter_eq_of_incident (self_mem_edgeComponent he₀) hv₀).symm

/-- **Odd boundary distributes over the connected-component decomposition**:
`∂X = ⊔_{C ∈ polymerDecomposition X} ∂C`.  Each vertex's incident `X`-edges lie in a single
component, so its `X`-parity equals its parity in that component. -/
theorem oddBoundary_biUnion_polymerDecomposition (X : Finset (Sym2 ι)) :
    oddBoundary X = (polymerDecomposition X).biUnion oddBoundary := by
  classical
  ext v
  rw [oddBoundary, Finset.mem_filter, Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hv
    have hpos : 0 < (X.filter (v ∈ ·)).card := by
      rcases hv with ⟨k, hk⟩
      rw [hk]
      omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at he
    refine ⟨edgeComponent X e, ?_, ?_⟩
    · rw [mem_polymerDecomposition]
      exact ⟨e, he.1, rfl⟩
    · rw [oddBoundary, Finset.mem_filter]
      refine ⟨Finset.mem_univ v, ?_⟩
      rw [← degree_eq_degree_component he.1 he.2]
      exact hv
  · rintro ⟨C, hC, hvC⟩
    rw [mem_polymerDecomposition] at hC
    obtain ⟨e, he, rfl⟩ := hC
    rw [oddBoundary, Finset.mem_filter] at hvC
    have hpos : 0 < ((edgeComponent X e).filter (v ∈ ·)).card := by
      rcases hvC.2 with ⟨k, hk⟩
      rw [hk]
      omega
    obtain ⟨f, hf⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hf
    rw [edgeComponent_filter_eq_of_incident hf.1 hf.2] at hvC
    exact hvC.2

omit [Fintype ι] [DecidableEq ι] in
/-- **Components stay inside `G.edgeFinset`**: `edgeComponent X e ⊆ X ⊆ G.edgeFinset`. -/
theorem edgeComponent_subset_edgeFinset (G : SimpleGraph ι) [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} (hX : X ∈ G.edgeFinset.powerset) (e : Sym2 ι) :
    edgeComponent X e ∈ G.edgeFinset.powerset := by
  rw [Finset.mem_powerset]
  exact (edgeComponent_subset X e).trans (Finset.mem_powerset.mp hX)

omit [Fintype ι] in
/-- **Every decomposition component is an edge subset of `G`** when `X` is. -/
theorem polymerDecomposition_subset_edgeFinset (G : SimpleGraph ι) [Fintype G.edgeSet]
    {X C : Finset (Sym2 ι)} (hX : X ∈ G.edgeFinset.powerset)
    (hC : C ∈ polymerDecomposition X) :
    C ∈ G.edgeFinset.powerset := by
  rw [mem_polymerDecomposition] at hC
  obtain ⟨e, _he, rfl⟩ := hC
  exact edgeComponent_subset_edgeFinset G hX e

omit [Fintype ι] in
/-- **A two-point-bounded set of even cardinality is `∅` or the pair**. -/
theorem finset_subset_pair_of_even_card {i j : ι} (hij : i ≠ j)
    {B : Finset ι} (hsub : B ⊆ ({i, j} : Finset ι)) (heven : Even B.card) :
    B = ∅ ∨ B = ({i, j} : Finset ι) := by
  classical
  have hle : B.card ≤ 2 := le_trans (Finset.card_le_card hsub) (by simp [Finset.card_pair hij])
  have hc : B.card = 0 ∨ B.card = 2 := by
    rcases heven with ⟨m, hm⟩
    omega
  rcases hc with h | h
  · exact Or.inl (Finset.card_eq_zero.mp h)
  · refine Or.inr (Finset.eq_of_subset_of_card_le hsub ?_)
    rw [Finset.card_pair hij]
    omega

/-- **A component meeting the pair carries the whole pair boundary**: if `∂C ⊆ {i,j}` and `∂C` is
nonempty, then `∂C = {i,j}` (handshake parity rules out a singleton boundary). -/
theorem oddBoundary_eq_pair_of_subset_pair_of_mem
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {C : Finset (Sym2 ι)} {i j v : ι}
    (hC : C ∈ G.edgeFinset.powerset) (hij : i ≠ j)
    (hsub : oddBoundary C ⊆ ({i, j} : Finset ι)) (hv : v ∈ oddBoundary C) :
    oddBoundary C = ({i, j} : Finset ι) := by
  rcases finset_subset_pair_of_even_card hij hsub (oddBoundary_card_even G hC) with h0 | hpair
  · rw [h0] at hv
    simp at hv
  · exact hpair

/-- **Unique connecting component** (GJ §18.4–18.7, FV §3.7.3): an edge subset `X` with two-point
odd boundary `∂X = {i,j}` (`i ≠ j`) has a *unique* connected component `C ∈ polymerDecomposition X`
with `∂C = {i,j}` — the open cluster linking the two sources.  Uniqueness is by vertex-disjointness
of the components (a second such component would also support `i`). -/
theorem existsUnique_component_oddBoundary_pair (G : SimpleGraph ι) [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} {i j : ι}
    (hX : X ∈ G.edgeFinset.powerset) (hij : i ≠ j)
    (hbd : oddBoundary X = ({i, j} : Finset ι)) :
    ∃! C, C ∈ polymerDecomposition X ∧ oddBoundary C = ({i, j} : Finset ι) := by
  classical
  have hiX : i ∈ oddBoundary X := by
    rw [hbd]
    simp
  rw [oddBoundary_biUnion_polymerDecomposition X, Finset.mem_biUnion] at hiX
  obtain ⟨C, hC, hiC⟩ := hiX
  have hCsub : oddBoundary C ⊆ ({i, j} : Finset ι) := by
    intro v hv
    have hvU : v ∈ (polymerDecomposition X).biUnion oddBoundary := by
      rw [Finset.mem_biUnion]
      exact ⟨C, hC, hv⟩
    rw [← oddBoundary_biUnion_polymerDecomposition X, hbd] at hvU
    exact hvU
  have hCbd : oddBoundary C = ({i, j} : Finset ι) :=
    oddBoundary_eq_pair_of_subset_pair_of_mem
      (G := G) (C := C) (i := i) (j := j) (v := i)
      (polymerDecomposition_subset_edgeFinset G hX hC) hij hCsub hiC
  refine ⟨C, ⟨hC, hCbd⟩, ?_⟩
  intro C' hC'
  obtain ⟨hC'mem, hC'bd⟩ := hC'
  by_cases hEq : C' = C
  · exact hEq
  · exfalso
    have hpairwise := polymerDecomposition_pairwise_vertexDisjoint (X := X)
    have hdisj : IsPolymerVertexDisjoint C' C :=
      hpairwise (Finset.mem_coe.mpr hC'mem) (Finset.mem_coe.mpr hC) hEq
    unfold IsPolymerVertexDisjoint at hdisj
    have hiC'sup : i ∈ polymerSupport C' := by
      apply oddBoundary_subset_polymerSupport C'
      rw [hC'bd]
      simp
    have hiCsup : i ∈ polymerSupport C := by
      apply oddBoundary_subset_polymerSupport C
      rw [hCbd]
      simp
    exact (Finset.disjoint_left.mp hdisj) hiC'sup hiCsup

end IsingModel
