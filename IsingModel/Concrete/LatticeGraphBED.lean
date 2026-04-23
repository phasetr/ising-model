import IsingModel.Concrete.CubicExhaustion
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Bounded edge density of `latticeGraph d` on cubic boxes

Combining `IsingModel/Concrete/CubicExhaustion.lean` (concrete
`Ambient.Exhaustion (Fin d → ℤ)`) with the lattice graph degree
bound, we prove
`Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d)
(Ambient.cubicExhaustion d)` with constant `c = d`.

## Main theorems

* `latticeGraph_adj_mem_neighborEnum` — every neighbour of `v` in
  `latticeGraph d` lies in a `2d`-element candidate set
  (`Function.update v i (v i ± 1)` over `i : Fin d`).
* `inducedLatticeGraph_degree_le` — induced-graph degree bounded by
  `2 * d` for every vertex.
* `boundedEdgeDensity_latticeGraph_cubicExhaustion` —
  `|E(latticeGraph d [Λ_n])| ≤ d · |Λ_n|`, via handshake.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.6, p. 67.
-/

namespace IsingModel

namespace Ambient

open Finset SimpleGraph

/-- **Candidate neighbours of `v` in `latticeGraph d`**: for `v : Fin d → ℤ`,
the `2d`-element set `{Function.update v i (v i + 1), Function.update v i (v i - 1)
| i : Fin d}` of possible ℓ¹-distance-1 neighbours. -/
noncomputable def latticeNeighborEnum (d : ℕ) (v : Fin d → ℤ) :
    Finset (Fin d → ℤ) :=
  (Finset.univ : Finset (Fin d)).biUnion (fun i =>
    ({Function.update v i (v i + 1),
      Function.update v i (v i - 1)} : Finset (Fin d → ℤ)))

/-- **Size bound on the neighbour-candidate set**:
`|latticeNeighborEnum d v| ≤ 2 * d`. -/
theorem latticeNeighborEnum_card_le (d : ℕ) (v : Fin d → ℤ) :
    (latticeNeighborEnum d v).card ≤ 2 * d := by
  unfold latticeNeighborEnum
  calc ((Finset.univ : Finset (Fin d)).biUnion (fun i =>
          ({Function.update v i (v i + 1),
            Function.update v i (v i - 1)} : Finset (Fin d → ℤ)))).card
      ≤ ∑ i : Fin d, (({Function.update v i (v i + 1),
                        Function.update v i (v i - 1)} :
                        Finset (Fin d → ℤ)).card) := Finset.card_biUnion_le
    _ ≤ ∑ _ : Fin d, 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.card_insert_le _ _ |>.trans (by simp)
    _ = 2 * d := by simp [Finset.sum_const, Finset.card_univ, mul_comm]

/-- **Every neighbour of `v` in `latticeGraph d` lies in `latticeNeighborEnum d v`**:
the `Adj` condition `∑ i, |v i - w i| = 1` forces exactly one coordinate
to differ by `±1`, so `w = Function.update v i (v i ± 1)` for some `i`. -/
theorem latticeGraph_adj_mem_neighborEnum (d : ℕ) (v w : Fin d → ℤ)
    (h : (IsingModel.latticeGraph d).Adj v w) :
    w ∈ latticeNeighborEnum d v := by
  -- `h` unfolds to `∑ i, |v i - w i| = 1`.
  have hsum : (∑ i : Fin d, |v i - w i|) = 1 := h
  -- Since the sum of non-negative integers equals 1, exactly one
  -- term is 1 and all others are 0.
  have hnonneg : ∀ i : Fin d, 0 ≤ |v i - w i| := fun i => abs_nonneg _
  -- There exists `i` with `|v i - w i| ≥ 1`, and in fact `= 1`;
  -- for all `j ≠ i`, `|v j - w j| = 0`.
  have hexist : ∃ i : Fin d, |v i - w i| = 1 := by
    by_contra hne
    push Not at hne
    -- Each |v i - w i| is ≠ 1, ≥ 0, integer ⇒ = 0 or ≥ 2.
    -- All zero: sum 0 ≠ 1. Some ≥ 2: sum ≥ 2 ≠ 1.
    have hall : ∀ i, |v i - w i| = 0 ∨ 2 ≤ |v i - w i| := by
      intro i
      specialize hne i
      rcases lt_or_ge (|v i - w i|) 1 with hlt | hge
      · left
        have : |v i - w i| = 0 := by
          have : (0 : ℤ) ≤ |v i - w i| := hnonneg i
          omega
        exact this
      · right
        -- `1 ≤ |·|` and `|·| ≠ 1` means `2 ≤ |·|`.
        omega
    by_cases hallz : ∀ i, |v i - w i| = 0
    · have : (∑ i : Fin d, |v i - w i|) = 0 := by
        rw [Finset.sum_eq_zero]
        intro i _
        exact hallz i
      omega
    · push Not at hallz
      obtain ⟨j, hj⟩ := hallz
      rcases hall j with h0 | h2
      · exact hj h0
      · have : 2 ≤ ∑ i : Fin d, |v i - w i| := by
          calc (2 : ℤ) ≤ |v j - w j| := h2
            _ ≤ ∑ i : Fin d, |v i - w i| :=
                Finset.single_le_sum (f := fun i => |v i - w i|)
                  (fun i _ => hnonneg i) (Finset.mem_univ j)
        omega
  obtain ⟨i, hi⟩ := hexist
  -- The `i`-th coordinate differs by ±1, all others agree.
  have hothers : ∀ j, j ≠ i → v j = w j := by
    intro j hji
    have hsum' : (∑ k : Fin d, |v k - w k|)
        = |v i - w i| + ∑ k ∈ Finset.univ.erase i, |v k - w k| := by
      rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i)]
      simp [Finset.sdiff_singleton_eq_erase, add_comm]
    rw [hi, hsum] at hsum'
    have hsum_erase : (∑ k ∈ Finset.univ.erase i, |v k - w k|) = 0 := by omega
    have hj_mem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩
    have hj_zero : |v j - w j| = 0 := by
      have hnn : ∀ k ∈ Finset.univ.erase i, 0 ≤ |v k - w k| := fun k _ => hnonneg k
      exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum_erase _ hj_mem
    have : v j - w j = 0 := by
      have := abs_eq_zero.mp hj_zero
      exact this
    linarith
  -- Therefore `w = Function.update v i (w i)` and `w i = v i ± 1`.
  have hvi_cases : w i = v i + 1 ∨ w i = v i - 1 := by
    have : |v i - w i| = 1 := hi
    rcases abs_eq (by norm_num : (0:ℤ) ≤ 1) |>.mp this with ha | hb
    · right; linarith
    · left; linarith
  have hw_eq : w = Function.update v i (w i) := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_apply, if_neg hk]
      exact (hothers k hk).symm
  unfold latticeNeighborEnum
  rw [Finset.mem_biUnion]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rcases hvi_cases with h1 | h2
  · rw [Finset.mem_insert, Finset.mem_singleton]
    left
    rw [hw_eq, h1]
  · rw [Finset.mem_insert, Finset.mem_singleton]
    right
    rw [hw_eq, h2]

/-- **`Fintype` instance for the neighbour set of `latticeGraph d`**:
every vertex `v : Fin d → ℤ` has finitely many neighbours,
exhibited as the filter of the candidate set
`latticeNeighborEnum d v` along the adjacency relation. By the
`abbrev` `SimpleGraph.LocallyFinite := ∀ v, Fintype (G.neighborSet v)`,
this also serves as the `LocallyFinite` instance for
`IsingModel.latticeGraph d`, unlocking the unrestricted
`neighborFinset` / `degree` API on the infinite vertex set. -/
noncomputable instance latticeGraph_neighborSet_fintype
    (d : ℕ) (v : Fin d → ℤ) :
    Fintype ((IsingModel.latticeGraph d).neighborSet v) :=
  Fintype.ofFinset
    ((latticeNeighborEnum d v).filter ((IsingModel.latticeGraph d).Adj v))
    (fun w => by
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborSet]
      refine ⟨fun h => h.2, fun hadj => ?_⟩
      exact ⟨latticeGraph_adj_mem_neighborEnum d v w hadj, hadj⟩)

/-- **Per-vertex degree bound for the unrestricted `latticeGraph d`**:
every vertex has degree at most `2 * d`. Companion of the
induced-subgraph version `inducedLatticeGraph_degree_le`, made
statable by the `latticeGraph_neighborSet_fintype` instance
above. The proof embeds `neighborFinset v` into
`latticeNeighborEnum d v` via `latticeGraph_adj_mem_neighborEnum`
and chains `Finset.card_le_card` with `latticeNeighborEnum_card_le`. -/
theorem latticeGraph_degree_le (d : ℕ) (v : Fin d → ℤ) :
    (IsingModel.latticeGraph d).degree v ≤ 2 * d := by
  have hsubset : (IsingModel.latticeGraph d).neighborFinset v ⊆
      latticeNeighborEnum d v := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    exact latticeGraph_adj_mem_neighborEnum d v w hw
  calc (IsingModel.latticeGraph d).degree v
      = ((IsingModel.latticeGraph d).neighborFinset v).card :=
        (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
    _ ≤ (latticeNeighborEnum d v).card := Finset.card_le_card hsubset
    _ ≤ 2 * d := latticeNeighborEnum_card_le d v

end Ambient

end IsingModel

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
for the Simon–Lieb inequality (Friedli–Velenik Prop 9.31, Glimm–
Jaffe §5.1). -/
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
monotonicity from PR #788's
`edgeBoundary_card_eq_sum_inner_filter` finishes. -/
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
(`G.symm` to swap adjacency). Sum monotonicity from PR #789's
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

end SimpleGraph

namespace IsingModel

namespace Ambient

open Finset SimpleGraph

/-- **ℤ^d boundary cardinality bound**: on `latticeGraph d`,
`|∂_o^v S| ≤ 2 * d * |S|`. Combines the generic
`SimpleGraph.outerVertexBoundary_card_le_sum_degrees` with the
per-vertex degree bound `latticeGraph_degree_le`. -/
theorem latticeGraph_outerVertexBoundary_card_le
    (d : ℕ) (S : Finset (Fin d → ℤ)) :
    ((IsingModel.latticeGraph d).outerVertexBoundary S).card
      ≤ 2 * d * S.card := by
  refine ((IsingModel.latticeGraph d).outerVertexBoundary_card_le_sum_degrees
    S).trans ?_
  calc (∑ x ∈ S, (IsingModel.latticeGraph d).degree x)
      ≤ ∑ _x ∈ S, 2 * d :=
        Finset.sum_le_sum (fun x _ => latticeGraph_degree_le d x)
    _ = 2 * d * S.card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **ℤ^d outer-by-inner boundary linear bound**: on
`latticeGraph d`, `|∂_o^v S| ≤ 2d · |∂_i^v S|`. Combines the
generic `SimpleGraph.outerVertexBoundary_card_le_sum_degrees_innerVertexBoundary`
with the per-vertex degree bound `latticeGraph_degree_le`. Each
inner-boundary vertex contributes at most `2d` outer-boundary
neighbours, giving the linear factor; this is the elementary
max-degree-based bound, not the optimal vertex-isoperimetric
inequality on `ℤ^d`. -/
theorem latticeGraph_outerVertexBoundary_card_le_two_mul_d_mul_innerVertexBoundary_card
    (d : ℕ) (S : Finset (Fin d → ℤ)) :
    ((IsingModel.latticeGraph d).outerVertexBoundary S).card
      ≤ 2 * d * ((IsingModel.latticeGraph d).innerVertexBoundary S).card := by
  refine ((IsingModel.latticeGraph d).outerVertexBoundary_card_le_sum_degrees_innerVertexBoundary
    S).trans ?_
  calc (∑ x ∈ (IsingModel.latticeGraph d).innerVertexBoundary S,
          (IsingModel.latticeGraph d).degree x)
      ≤ ∑ _x ∈ (IsingModel.latticeGraph d).innerVertexBoundary S, 2 * d :=
        Finset.sum_le_sum (fun x _ => latticeGraph_degree_le d x)
    _ = 2 * d * ((IsingModel.latticeGraph d).innerVertexBoundary S).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **ℤ^d edge boundary linear bound**: on `latticeGraph d`,
`|∂^e S| ≤ 2d · |∂_i^v S|`. Combines the generic
`SimpleGraph.edgeBoundary_card_le_sum_degrees_innerVertexBoundary`
with the per-vertex degree bound `latticeGraph_degree_le`. -/
theorem latticeGraph_edgeBoundary_card_le_two_mul_d_mul_innerVertexBoundary_card
    (d : ℕ) (S : Finset (Fin d → ℤ)) :
    ((IsingModel.latticeGraph d).edgeBoundary S).card
      ≤ 2 * d * ((IsingModel.latticeGraph d).innerVertexBoundary S).card := by
  refine ((IsingModel.latticeGraph d).edgeBoundary_card_le_sum_degrees_innerVertexBoundary
    S).trans ?_
  calc (∑ x ∈ (IsingModel.latticeGraph d).innerVertexBoundary S,
          (IsingModel.latticeGraph d).degree x)
      ≤ ∑ _x ∈ (IsingModel.latticeGraph d).innerVertexBoundary S, 2 * d :=
        Finset.sum_le_sum (fun x _ => latticeGraph_degree_le d x)
    _ = 2 * d * ((IsingModel.latticeGraph d).innerVertexBoundary S).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- Decidable-Adj instance for the induced lattice graph.

Provided explicitly because the generic `instDecidableRel_induce_adj`
does not fire through the `noncomputable def Ambient.inducedGraph`
wrapper automatically. -/
instance (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    DecidableRel (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).Adj :=
  fun ⟨a, _⟩ ⟨b, _⟩ => by
    unfold Ambient.inducedGraph SimpleGraph.induce
    exact inferInstance

/-- Fintype instance for the edge set of the induced lattice graph
on a cubic box.

Provided explicitly to thread through `Ambient.inducedGraph` — the
generic `SimpleGraph.fintypeEdgeSet` would fire directly on
`SimpleGraph.induce` but the `noncomputable def` wrapper masks this. -/
noncomputable instance (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet := by
  haveI : Fintype (↑Λ : Type _) := inferInstance
  haveI : Fintype (Sym2 ↑Λ) := inferInstance
  exact SimpleGraph.fintypeEdgeSet _

/-- **Per-vertex degree bound for the induced lattice graph**: every
vertex in the induced subgraph on `Λ` has degree at most `2 * d`. -/
theorem inducedLatticeGraph_degree_le (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (v : ↑Λ) :
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).degree v ≤ 2 * d := by
  -- degree = |neighborFinset|; each neighbor w has w.val ∈ latticeNeighborEnum d v.val.
  classical
  unfold SimpleGraph.degree
  -- `neighborFinset v` is a Finset of `↑Λ`; its card is bounded by |latticeNeighborEnum d v.val|.
  set nf := (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).neighborFinset v
  have himg : nf.image Subtype.val ⊆ latticeNeighborEnum d v.val := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨⟨x, hx⟩, hxmem, hxval⟩ := hw
    subst hxval
    -- `⟨x, hx⟩ ∈ nf` means adjacency in the induced graph.
    have hadj : (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).Adj v ⟨x, hx⟩ :=
      (SimpleGraph.mem_neighborFinset _ _ _).mp hxmem
    -- Adjacency in `inducedGraph G Λ = G.induce ↑Λ` gives `G.Adj v.val x`.
    have : (IsingModel.latticeGraph d).Adj v.val x := by
      simp only [Ambient.inducedGraph, SimpleGraph.induce_adj] at hadj
      exact hadj
    exact latticeGraph_adj_mem_neighborEnum d v.val x this
  have h_card_img : (nf.image Subtype.val).card ≤ (latticeNeighborEnum d v.val).card :=
    Finset.card_le_card himg
  have h_inj : Set.InjOn Subtype.val (nf : Set ↑Λ) := by
    intro a _ b _ hab
    exact Subtype.ext hab
  have h_card_eq : (nf.image Subtype.val).card = nf.card :=
    Finset.card_image_of_injOn h_inj
  rw [← h_card_eq]
  exact h_card_img.trans (latticeNeighborEnum_card_le d v.val)

/-- **Handshake bound**: on the induced lattice graph,
`|E| ≤ d · |Λ|`. -/
theorem inducedLatticeGraph_card_edgeFinset_le (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    ((Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ)
      ≤ d * Fintype.card (↑Λ : Type _) := by
  -- 2|E| = ∑ degree ≤ 2d · |V|.
  have hdeg :
      ∑ v : ↑Λ, (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).degree v
        ≤ 2 * d * Fintype.card (↑Λ : Type _) := by
    calc ∑ v : ↑Λ, (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).degree v
        ≤ ∑ _ : ↑Λ, (2 * d : ℕ) :=
          Finset.sum_le_sum (fun v _ => inducedLatticeGraph_degree_le d Λ v)
      _ = Fintype.card (↑Λ : Type _) * (2 * d) := by
          simp [Finset.sum_const, mul_comm]
      _ = 2 * d * Fintype.card (↑Λ : Type _) := by ring
  have hhand :
      (2 * (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        : ℕ) = ∑ v, (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).degree v := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
  have hbnd :
      (2 * (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        : ℕ) ≤ 2 * d * Fintype.card (↑Λ : Type _) := by
    rw [hhand]; exact hdeg
  -- Divide by 2 (integer-level): 2|E| ≤ 2d|V| ⇒ |E| ≤ d|V|.
  have : ((Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        : ℕ) ≤ d * Fintype.card (↑Λ : Type _) := by
    have h2 : 2 * ((Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℕ)
      ≤ 2 * (d * Fintype.card (↑Λ : Type _)) := by
      calc 2 * ((Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℕ)
          ≤ 2 * d * Fintype.card (↑Λ : Type _) := hbnd
        _ = 2 * (d * Fintype.card (↑Λ : Type _)) := by ring
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  -- Cast to ℝ.
  exact_mod_cast this

/-- **Bounded edge density for `latticeGraph d` along `cubicExhaustion d`**:
`|E(latticeGraph d [Λ_n])| ≤ d · |Λ_n|` for every `n`. -/
theorem boundedEdgeDensity_latticeGraph_cubicExhaustion (d : ℕ) :
    Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) := by
  refine ⟨(d : ℝ), ?_⟩
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d ((Ambient.cubicExhaustion d).volume n)

end Ambient

end IsingModel
