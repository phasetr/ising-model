import IsingModel.Concrete.LatticeGraphBED.HandshakeIdentity

/-!
# Lattice graph bounded edge density split — outer/inner vertex boundary and edge boundary

Part of the split lattice-graph bounded-edge-density layer (Issue #1850).
-/

/-! ## Outer vertex boundary of a Finset in a locally finite graph

Generic graph-theoretic API placed in mathlib's `SimpleGraph`
namespace: the outer vertex boundary
`∂_o^v S = (⋃_{x ∈ S} N_G(x)) \ S` of a finite Finset `S` in any
locally finite simple graph, with four basic lemmas. The
`latticeGraph d`-specific cardinality wrapper
`|∂_o^v S| ≤ 2d · |S|` lives back in `IsingModel.Ambient` below. -/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- **Outer vertex boundary** of a finite Finset `S` in a locally
finite simple graph: vertices not in `S` that have a neighbour in
`S`. Formally `S.biUnion G.neighborFinset \ S`. Preparatory notion
for the Simon–Lieb inequality (Simon 1980, Comm. Math. Phys. 77,
111–126; Lieb 1980, Comm. Math. Phys. 77, 127–135). -/
def outerVertexBoundary [DecidableEq V] [LocallyFinite G]
    (S : Finset V) : Finset V :=
  S.biUnion (fun v => G.neighborFinset v) \ S

/-- **Membership in `outerVertexBoundary G S`**: `y` is in the
outer vertex boundary iff `y` is outside `S` and has at least one
neighbour inside `S`. -/
lemma mem_outerVertexBoundary_iff [DecidableEq V] [LocallyFinite G]
    (S : Finset V) (y : V) :
    y ∈ G.outerVertexBoundary S
      ↔ y ∉ S ∧ ∃ x ∈ S, G.Adj x y := by
  simp only [outerVertexBoundary, Finset.mem_sdiff, Finset.mem_biUnion,
    mem_neighborFinset, and_comm]

/-- **Disjointness**: `outerVertexBoundary G S` is disjoint from
`S`. Immediate from the membership characterisation, since every
boundary point lies outside `S`. -/
lemma outerVertexBoundary_disjoint [DecidableEq V] [LocallyFinite G]
    (S : Finset V) :
    Disjoint (G.outerVertexBoundary S) S := by
  rw [Finset.disjoint_left]
  intro y hy hyS
  exact ((G.mem_outerVertexBoundary_iff S y).mp hy).1 hyS

/-- **Empty boundary of empty set**: the outer vertex boundary of
`∅` is `∅`. The `biUnion` over an empty Finset is empty, hence
the set difference is empty. -/
lemma outerVertexBoundary_empty [DecidableEq V] [LocallyFinite G] :
    G.outerVertexBoundary (∅ : Finset V) = ∅ := by
  simp [outerVertexBoundary]

/-- **Cardinality bound by sum of degrees**:
`|∂_o^v S| ≤ ∑_{x ∈ S} deg_G(x)`. The boundary is a subset of
`S.biUnion G.neighborFinset` whose cardinality is bounded by the
sum of `|N_G(x)|` (`Finset.card_biUnion_le`); each
`|N_G(x)| = deg_G(x)` by `card_neighborFinset_eq_degree`. -/
lemma outerVertexBoundary_card_le_sum_degrees [DecidableEq V]
    [LocallyFinite G] (S : Finset V) :
    (G.outerVertexBoundary S).card ≤ ∑ x ∈ S, G.degree x := by
  have hsubset : G.outerVertexBoundary S
      ⊆ S.biUnion (fun v => G.neighborFinset v) :=
    Finset.sdiff_subset
  refine (Finset.card_le_card hsubset).trans ?_
  refine (Finset.card_biUnion_le).trans ?_
  exact Finset.sum_le_sum (fun x _ =>
    (card_neighborFinset_eq_degree _ _).le)

/-- **Inner vertex boundary** of a finite Finset `S` in a locally
finite simple graph: vertices of `S` that have at least one
neighbour outside `S`. Formally
`S.filter (fun x => ¬ (G.neighborFinset x ⊆ S))`. Companion to
`outerVertexBoundary`. -/
def innerVertexBoundary [DecidableEq V] [LocallyFinite G]
    (S : Finset V) : Finset V :=
  S.filter (fun x => ¬ (G.neighborFinset x ⊆ S))

/-- **Membership in `innerVertexBoundary G S`**: `x` is in the
inner vertex boundary iff `x` is in `S` and has at least one
neighbour outside `S`. -/
lemma mem_innerVertexBoundary_iff [DecidableEq V] [LocallyFinite G]
    (S : Finset V) (x : V) :
    x ∈ G.innerVertexBoundary S
      ↔ x ∈ S ∧ ∃ y, G.Adj x y ∧ y ∉ S := by
  simp only [innerVertexBoundary, Finset.mem_filter, Finset.not_subset,
    mem_neighborFinset]

/-- **Subset of self**: the inner vertex boundary is a subset of
`S`. Direct from the `Finset.filter` definition. -/
lemma innerVertexBoundary_subset_self [DecidableEq V] [LocallyFinite G]
    (S : Finset V) :
    G.innerVertexBoundary S ⊆ S :=
  Finset.filter_subset _ _

/-- **Empty boundary of empty set**: the inner vertex boundary of
`∅` is `∅`, since `Finset.filter` on the empty Finset is empty. -/
lemma innerVertexBoundary_empty [DecidableEq V] [LocallyFinite G] :
    G.innerVertexBoundary (∅ : Finset V) = ∅ := by
  simp [innerVertexBoundary]

/-- **Outer-by-inner boundary degree bound**:
`|∂_o^v S| ≤ ∑_{x ∈ ∂_i^v S} deg_G(x)`. Every outer-boundary
vertex `y` is reached as a neighbour of some inner-boundary
vertex `x`: the witness `x ∈ S` of `y ∈ outerVertexBoundary G S`
has the outside neighbour `y`, so `x ∈ innerVertexBoundary G S`.
Hence
`outerVertexBoundary G S ⊆ (innerVertexBoundary G S).biUnion neighborFinset`,
and `Finset.card_biUnion_le` + `card_neighborFinset_eq_degree`
finishes. The outer boundary is upper-bounded by a sum of degrees
ranging only over the (typically much smaller) inner boundary. -/
lemma outerVertexBoundary_card_le_sum_degrees_innerVertexBoundary
    [DecidableEq V] [LocallyFinite G] (S : Finset V) :
    (G.outerVertexBoundary S).card
      ≤ ∑ x ∈ G.innerVertexBoundary S, G.degree x := by
  have hsubset : G.outerVertexBoundary S
      ⊆ (G.innerVertexBoundary S).biUnion
          (fun v => G.neighborFinset v) := by
    intro y hy
    rw [G.mem_outerVertexBoundary_iff] at hy
    obtain ⟨hy_notS, x, hxS, hadj⟩ := hy
    refine Finset.mem_biUnion.mpr ⟨x, ?_, ?_⟩
    · rw [G.mem_innerVertexBoundary_iff]
      exact ⟨hxS, y, hadj, hy_notS⟩
    · exact (mem_neighborFinset _ _ _).mpr hadj
  refine (Finset.card_le_card hsubset).trans ?_
  refine (Finset.card_biUnion_le).trans ?_
  exact Finset.sum_le_sum (fun x _ =>
    (card_neighborFinset_eq_degree _ _).le)

/-- **Oriented edge boundary** of a finite Finset `S` in a
locally finite simple graph: ordered pairs `(x, y)` with
`x ∈ S`, `y ∉ S`, `G.Adj x y`. Each crossing edge is recorded
exactly once with its `S`-endpoint listed first, so no
double-counting. The "orientation" here is cut-induced (the
`S`-endpoint comes first), not a graph orientation; the form
sidesteps the `Sym2 V` quotient handling that an unordered
formulation would force. -/
def edgeBoundary [DecidableEq V] [LocallyFinite G]
    (S : Finset V) : Finset (V × V) :=
  (G.innerVertexBoundary S).biUnion fun x =>
    ((G.neighborFinset x).filter (fun y => y ∉ S)).image
      (fun y => (x, y))

/-- **Membership in `edgeBoundary G S`**: `(x, y)` is in the
oriented edge boundary iff `x ∈ S`, `y ∉ S`, and `G.Adj x y`. -/
lemma mem_edgeBoundary_iff [DecidableEq V] [LocallyFinite G]
    (S : Finset V) (e : V × V) :
    e ∈ G.edgeBoundary S
      ↔ e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2 := by
  obtain ⟨x, y⟩ := e
  simp only [edgeBoundary, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_filter, mem_neighborFinset, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rintro ⟨a, ha, b, ⟨hab, hbS⟩, hrfla, hrflb⟩
    -- `(a, b) = (x, y)` ⇒ `a = x`, `b = y`
    subst hrfla
    subst hrflb
    rw [G.mem_innerVertexBoundary_iff] at ha
    exact ⟨ha.1, hbS, hab⟩
  · rintro ⟨hxS, hyS, hadj⟩
    refine ⟨x, ?_, y, ⟨hadj, hyS⟩, rfl, rfl⟩
    rw [G.mem_innerVertexBoundary_iff]
    exact ⟨hxS, y, hadj, hyS⟩

/-- **Empty boundary of empty set**: `edgeBoundary G ∅ = ∅`,
since `innerVertexBoundary G ∅ = ∅` (PR #786) collapses the
outer `biUnion` to the empty Finset. -/
lemma edgeBoundary_empty [DecidableEq V] [LocallyFinite G] :
    G.edgeBoundary (∅ : Finset V) = ∅ := by
  simp [edgeBoundary, G.innerVertexBoundary_empty]

/-- **Cardinality bound by sum of degrees over the inner
boundary**: `|∂^e S| ≤ ∑_{x ∈ ∂_i^v S} deg_G(x)`. Each
`x ∈ innerVertexBoundary` contributes at most
`|G.neighborFinset x| = deg_G(x)` oriented edges: the image of
the filtered neighbour Finset under `y ↦ (x, y)` is no larger
than the filter, which is no larger than the neighbour Finset.
`Finset.card_biUnion_le` then sums these bounds. -/
lemma edgeBoundary_card_le_sum_degrees_innerVertexBoundary
    [DecidableEq V] [LocallyFinite G] (S : Finset V) :
    (G.edgeBoundary S).card
      ≤ ∑ x ∈ G.innerVertexBoundary S, G.degree x := by
  refine (Finset.card_biUnion_le).trans ?_
  refine Finset.sum_le_sum (fun x _ => ?_)
  refine (Finset.card_image_le).trans ?_
  refine (Finset.card_filter_le _ _).trans ?_
  exact (card_neighborFinset_eq_degree _ _).le

/-- **Edge boundary cardinality as a closed sum over the inner
boundary**: strengthens `edgeBoundary_card_le_sum_degrees_innerVertexBoundary`
to an equality. Two ingredients: (i) the `biUnion` defining
`edgeBoundary G S` is disjoint across
`x ∈ innerVertexBoundary G S` (different first coordinates), so
`Finset.card_biUnion` rewrites `card biUnion` to `∑ card`;
(ii) for fixed `x`, the embedding `y ↦ (x, y)` is injective, so
`Finset.card_image_of_injective` makes each summand's image
cardinality equal to the underlying filter's cardinality.
Bounding each filter cardinality by `(G.neighborFinset x).card =
G.degree x` recovers the previous inequality. -/
lemma edgeBoundary_card_eq_sum_inner_filter
    [DecidableEq V] [LocallyFinite G] (S : Finset V) :
    (G.edgeBoundary S).card
      = ∑ x ∈ G.innerVertexBoundary S,
          ((G.neighborFinset x).filter (fun y => y ∉ S)).card := by
  unfold edgeBoundary
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    refine Finset.card_image_of_injective _ ?_
    intro y₁ y₂ hy
    exact (Prod.mk.injEq _ _ _ _).mp hy |>.2
  · intro x _ x' _ hxx'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_image] at hp1 hp2
    obtain ⟨a, _, ha⟩ := hp1
    obtain ⟨b, _, hb⟩ := hp2
    apply hxx'
    have : (x, a) = (x', b) := ha.trans hb.symm
    exact ((Prod.mk.injEq _ _ _ _).mp this).1

/-- **Edge boundary cardinality as a sum over the outer vertex
boundary**: companion of `edgeBoundary_card_eq_sum_inner_filter`,
counting crossing edges by their *outside* endpoint instead of
their inside endpoint.

The proof rewrites `edgeBoundary G S` as a disjoint `biUnion`
indexed by the outer-boundary vertex `y`, then chains
`Finset.card_biUnion` (disjointness across distinct second
coordinates) with `Finset.card_image_of_injective`
(`x ↦ (x, y)` is injective in `x` for fixed `y`).

Combined with `edgeBoundary_card_eq_sum_inner_filter` this yields
the double-counting identity
`∑ x ∈ ∂_i^v S, |N(x) \ S| = ∑ y ∈ ∂_o^v S, |N(y) ∩ S|`. -/
lemma edgeBoundary_card_eq_sum_outer_filter
    [DecidableEq V] [LocallyFinite G] (S : Finset V) :
    (G.edgeBoundary S).card
      = ∑ y ∈ G.outerVertexBoundary S,
          ((G.neighborFinset y).filter (fun x => x ∈ S)).card := by
  -- Reorganise edgeBoundary as a disjoint biUnion indexed by `y`.
  have hrewrite :
      G.edgeBoundary S
        = (G.outerVertexBoundary S).biUnion fun y =>
            ((G.neighborFinset y).filter (fun x => x ∈ S)).image
              (fun x => (x, y)) := by
    ext ⟨x, y⟩
    simp only [G.mem_edgeBoundary_iff, Finset.mem_biUnion,
      Finset.mem_image, Finset.mem_filter, mem_neighborFinset,
      G.mem_outerVertexBoundary_iff, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rintro ⟨hxS, hyS, hadj⟩
      -- y is in outer boundary via x, and x is a neighbour of y in S.
      refine ⟨y, ⟨hyS, x, hxS, hadj⟩, x, ⟨G.symm hadj, hxS⟩, rfl, rfl⟩
    · rintro ⟨y', ⟨hyS, _⟩, x', ⟨hadj', hx'S⟩, rfl, rfl⟩
      -- After matching `rfl, rfl`, x' = x and y' = y already.
      exact ⟨hx'S, hyS, G.symm hadj'⟩
  rw [hrewrite, Finset.card_biUnion]
  · refine Finset.sum_congr rfl (fun y _ => ?_)
    refine Finset.card_image_of_injective _ ?_
    intro x₁ x₂ hx
    exact ((Prod.mk.injEq _ _ _ _).mp hx).1
  · intro y _ y' _ hyy'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_image] at hp1 hp2
    obtain ⟨a, _, ha⟩ := hp1
    obtain ⟨b, _, hb⟩ := hp2
    apply hyy'
    have : (a, y) = (b, y') := ha.trans hb.symm
    exact ((Prod.mk.injEq _ _ _ _).mp this).2

/-- **Inner vertex boundary by edge bound**:
`|∂_i^v S| ≤ |∂^e S|`. Each `x ∈ ∂_i^v S` has a witness
neighbour `y ∉ S` (from `mem_innerVertexBoundary_iff`), so the
filter `(N(x)).filter (· ∉ S)` has cardinality `≥ 1`. Sum
monotonicity through `edgeBoundary_card_eq_sum_inner_filter`
finishes. -/
lemma innerVertexBoundary_card_le_edgeBoundary_card
    [DecidableEq V] [LocallyFinite G] (S : Finset V) :
    (G.innerVertexBoundary S).card ≤ (G.edgeBoundary S).card := by
  rw [G.edgeBoundary_card_eq_sum_inner_filter S,
    Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum (fun x hx => ?_)
  rw [G.mem_innerVertexBoundary_iff] at hx
  obtain ⟨_, y, hadj, hyS⟩ := hx
  have hy_mem : y ∈ ((G.neighborFinset x).filter (fun y => y ∉ S)) :=
    Finset.mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr hadj, hyS⟩
  exact Finset.card_pos.mpr ⟨y, hy_mem⟩

/-- **Outer vertex boundary by edge bound**:
`|∂_o^v S| ≤ |∂^e S|`. Each `y ∈ ∂_o^v S` has a witness
neighbour `x ∈ S` (from `mem_outerVertexBoundary_iff`), so the
filter `(N(y)).filter (· ∈ S)` has cardinality `≥ 1`
(`G.symm` to swap adjacency). Sum monotonicity through
`edgeBoundary_card_eq_sum_outer_filter` finishes. -/
lemma outerVertexBoundary_card_le_edgeBoundary_card
    [DecidableEq V] [LocallyFinite G] (S : Finset V) :
    (G.outerVertexBoundary S).card ≤ (G.edgeBoundary S).card := by
  rw [G.edgeBoundary_card_eq_sum_outer_filter S,
    Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum (fun y hy => ?_)
  rw [G.mem_outerVertexBoundary_iff] at hy
  obtain ⟨_, x, hxS, hadj⟩ := hy
  have hx_mem : x ∈ ((G.neighborFinset y).filter (fun x => x ∈ S)) :=
    Finset.mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr (G.symm hadj), hxS⟩
  exact Finset.card_pos.mpr ⟨x, hx_mem⟩

/-- **Edge boundary card by outer-side degree sum**:
`(∂^e S).card ≤ ∑ y ∈ ∂_o^v S, G.degree y`. Symmetric companion
to `edgeBoundary_card_le_sum_degrees_innerVertexBoundary`. The
proof reduces to the outer-side equality
`edgeBoundary_card_eq_sum_outer_filter` and bounds each
`((G.neighborFinset y).filter (· ∈ S)).card` by
`(G.neighborFinset y).card = G.degree y`. -/
lemma edgeBoundary_card_le_sum_degrees_outerVertexBoundary
    [DecidableEq V] [LocallyFinite G] (S : Finset V) :
    (G.edgeBoundary S).card
      ≤ ∑ y ∈ G.outerVertexBoundary S, G.degree y := by
  rw [G.edgeBoundary_card_eq_sum_outer_filter S]
  refine Finset.sum_le_sum (fun y _ => ?_)
  refine (Finset.card_filter_le _ _).trans ?_
  exact (card_neighborFinset_eq_degree _ _).le

end SimpleGraph
