import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Edge-set decomposition for the disjoint sum graph

Basic edge-set identities for `SimpleGraph.sum` (the disjoint sum
`G ⊕g H`). These are infrastructure for the thermodynamic-limit
argument of Glimm–Jaffe *Quantum Physics* (2nd ed.) §4.6 (pp. 70ff):
on the disjoint sum graph the partition function factorizes,
`Z_{G ⊕g H}(p) = Z_G(p) · Z_H(p)`, and therefore the log-partition
function is additive, `log Z_{G ⊕g H} = log Z_G + log Z_H`. This
additive identity is the combinatorial root of the super-additivity
property of `log Z` over unions of disjoint sub-lattices, which in
turn yields convergence of the free-energy density
`f_Λ := (log Z_Λ) / |Λ|` via Fekete's lemma.

The file proves the single combinatorial ingredient that Hamiltonian
splitting on disjoint sums requires: the edge set of `G ⊕g H` is
the disjoint union of the images of the summands' edge sets under
the canonical `Sum.inl` / `Sum.inr` embeddings.

## Main declarations

* `SimpleGraph.sum_eq_map_sup` — `G ⊕g H` equals the join of the
  pushforwards of `G` and `H` along `Function.Embedding.inl` and
  `Function.Embedding.inr`.
* `SimpleGraph.edgeSet_sum` — edge-set decomposition as a union of
  `Sym2`-level images.
* `SimpleGraph.disjoint_inl_inr_edgeSet` — the two Set-level images are
  disjoint.
* `SimpleGraph.edgeSet_sum_finite` / `fintypeEdgeSetSum` — finiteness
  of the sum edge set from finiteness of the summands' edge sets.
* `SimpleGraph.edgeFinset_sum` — `Finset`-level decomposition.
* `SimpleGraph.disjoint_inl_inr_edgeFinset` — `Finset`-level disjointness
  of the two images.
* `SimpleGraph.card_edgeFinset_sum` — cardinality identity.
-/

namespace SimpleGraph

variable {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)

/-- The disjoint sum `G ⊕g H` equals the join of the pushforwards of
`G` along `Sum.inl` and of `H` along `Sum.inr`.

Case analysis on the two vertex arguments in `V ⊕ W`:
on the diagonal (`inl,inl` / `inr,inr`) the sum-graph adjacency
reduces to the original adjacency while the opposite `map`-summand
vanishes by constructor disjointness; in the off-diagonal
(`inl,inr` / `inr,inl`) both sides evaluate to `False`. -/
theorem sum_eq_map_sup :
    G.sum H = G.map (Function.Embedding.inl : V ↪ V ⊕ W)
              ⊔ H.map (Function.Embedding.inr : W ↪ V ⊕ W) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [sum_adj, sup_adj, map_adj',
               Function.Embedding.inl_apply, Function.Embedding.inr_apply,
               Sum.inl.injEq, Sum.inr.injEq, ne_eq, reduceCtorEq,
               and_false, false_and, exists_false,
               or_false, false_or, exists_eq_right_right, exists_eq_right]
  · exact ⟨fun h => ⟨h.ne, h⟩, fun ⟨_, h⟩ => h⟩
  · exact ⟨fun h => ⟨h.ne, h⟩, fun ⟨_, h⟩ => h⟩

/-- Edge-set decomposition: edges of `G ⊕g H` are the union of edges
pushed forward from `G` via `Sum.inl` and from `H` via `Sum.inr`. -/
theorem edgeSet_sum :
    (G.sum H).edgeSet =
      (Function.Embedding.inl : V ↪ V ⊕ W).sym2Map '' G.edgeSet ∪
      (Function.Embedding.inr : W ↪ V ⊕ W).sym2Map '' H.edgeSet := by
  rw [sum_eq_map_sup, edgeSet_sup, edgeSet_map, edgeSet_map]

/-- The two images in `edgeSet_sum` are disjoint: an edge of form
`s(Sum.inl v₁, Sum.inl v₂)` cannot equal an edge of form
`s(Sum.inr w₁, Sum.inr w₂)`. -/
theorem disjoint_inl_inr_edgeSet :
    Disjoint
      ((Function.Embedding.inl : V ↪ V ⊕ W).sym2Map '' G.edgeSet)
      ((Function.Embedding.inr : W ↪ V ⊕ W).sym2Map '' H.edgeSet) := by
  rw [Set.disjoint_iff]
  rintro e ⟨⟨eG, _, rfl⟩, ⟨eH, _, hEq⟩⟩
  refine Sym2.inductionOn₂ eG eH
    (fun v₁ v₂ w₁ w₂ (hEq : Sym2.map _ s(w₁, w₂) = Sym2.map _ s(v₁, v₂)) => ?_) hEq
  simp only [Sym2.map_mk, Function.Embedding.inl_apply, Function.Embedding.inr_apply,
             Sym2.eq_iff] at hEq
  rcases hEq with ⟨h, _⟩ | ⟨h, _⟩ <;> exact nomatch h

/-- The edge set of `G ⊕g H` is finite whenever both summands' edge
sets are finite (expressed via `Set.Finite`). -/
theorem edgeSet_sum_finite (hG : G.edgeSet.Finite) (hH : H.edgeSet.Finite) :
    (G.sum H).edgeSet.Finite := by
  rw [edgeSet_sum]
  exact (hG.image _).union (hH.image _)

/-- Fintype instance for `(G ⊕g H).edgeSet` from Fintype on the
summand edge sets. -/
noncomputable instance fintypeEdgeSetSum
    [Fintype G.edgeSet] [Fintype H.edgeSet] : Fintype (G.sum H).edgeSet :=
  (edgeSet_sum_finite G H (Set.toFinite _) (Set.toFinite _)).fintype

/-- Finset-level decomposition: `(G ⊕g H).edgeFinset` equals the union
of the two image finsets. The `[DecidableEq V]` / `[DecidableEq W]`
instances are required to express the Finset union `∪` in the target. -/
theorem edgeFinset_sum [DecidableEq V] [DecidableEq W]
    [Fintype G.edgeSet] [Fintype H.edgeSet] :
    (G.sum H).edgeFinset =
      G.edgeFinset.map (Function.Embedding.inl : V ↪ V ⊕ W).sym2Map ∪
      H.edgeFinset.map (Function.Embedding.inr : W ↪ V ⊕ W).sym2Map := by
  classical
  apply Finset.coe_injective
  rw [Finset.coe_union, coe_edgeFinset, Finset.coe_map, Finset.coe_map,
      coe_edgeFinset, coe_edgeFinset, edgeSet_sum]

/-- Finset-level disjointness: the two image finsets in `edgeFinset_sum`
are disjoint. Derived from the Set-level `disjoint_inl_inr_edgeSet`
by pushing disjointness through `Finset.coe`. -/
theorem disjoint_inl_inr_edgeFinset [Fintype G.edgeSet] [Fintype H.edgeSet] :
    Disjoint
      (G.edgeFinset.map (Function.Embedding.inl : V ↪ V ⊕ W).sym2Map)
      (H.edgeFinset.map (Function.Embedding.inr : W ↪ V ⊕ W).sym2Map) := by
  rw [← Finset.disjoint_coe, Finset.coe_map, Finset.coe_map,
      coe_edgeFinset, coe_edgeFinset]
  exact disjoint_inl_inr_edgeSet G H

/-- Cardinality identity:
`(G ⊕g H).edgeFinset.card = G.edgeFinset.card + H.edgeFinset.card`.

Classical decidability of `V` and `W` is introduced in the proof to
invoke `edgeFinset_sum` and `disjoint_inl_inr_edgeFinset`; these
instances do not appear in the type. -/
theorem card_edgeFinset_sum [Fintype G.edgeSet] [Fintype H.edgeSet] :
    (G.sum H).edgeFinset.card = G.edgeFinset.card + H.edgeFinset.card := by
  classical
  rw [edgeFinset_sum,
      Finset.card_union_of_disjoint (disjoint_inl_inr_edgeFinset G H),
      Finset.card_map, Finset.card_map]

end SimpleGraph
