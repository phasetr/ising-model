import IsingModel.AmbientLattice

/-!
# Translation invariance scaffolding for GJ §4.6 Prop 4.6.1

Lay out the minimal structures needed to state and (eventually) derive
the translation-invariance-based automatic proof of
`hcard_add`/`hsuper` in `freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses`.

Under an additive group `T` acting on the vertex type `V`, with a graph
`G : SimpleGraph V` whose edge relation is preserved by all translations,
and an exhaustion `Λ : Ambient.Exhaustion V` where consecutive
volumes differ by a disjoint translate of a fixed base block, the
hypotheses of `DisjointTowerHypotheses` are structural consequences
rather than user inputs. Fleshing out that chain is a multi-PR
programme (per CLAUDE.local.md workflow); this file provides the
starting definitions.

## Main definitions

* `IsingModel.Ambient.IsTranslationInvariant G`: a `SimpleGraph V`
  whose edge relation is preserved by all elements of an ambient
  `AddAction T V`.

## Examples

* The edgeless graph `(⊥ : SimpleGraph V)` is trivially translation
  invariant under any `AddAction`.

## References

* Glimm, J. and Jaffe, A., *Quantum Physics: A Functional Integral
  Point of View*, 2nd ed., Springer 1987, §4.6 Prop 4.6.1, p. 64.
-/

universe u v

namespace IsingModel

namespace Ambient

/-- A simple graph `G : SimpleGraph V` is **translation invariant**
under an `AddAction T V` if the edge relation is preserved by every
translation `t +ᵥ ·`:
`G.Adj (t +ᵥ u) (t +ᵥ v) ↔ G.Adj u v` for all `t : T`, `u v : V`.

Informally: translating the endpoints of an edge yields another edge
iff the original is; the graph looks the same everywhere.

This is the minimal structural datum behind the automatic
super-additivity of `log Z` along translation-invariant exhaustions
(GJ §4.6 Prop 4.6.1 p. 64). The translation-invariance-driven
derivation of `DisjointTowerHypotheses.super` from this predicate is
deferred to a subsequent PR. -/
class IsTranslationInvariant (T : Type u) [AddGroup T]
    {V : Type v} [AddAction T V] (G : SimpleGraph V) : Prop where
  /-- Every translation preserves the edge relation in both directions. -/
  adj_vadd : ∀ (t : T) (u v : V), G.Adj (t +ᵥ u) (t +ᵥ v) ↔ G.Adj u v

/-- **Edgeless graph is translation invariant**: `(⊥ : SimpleGraph V)`
has no edges, so the equivalence
`(⊥).Adj (t +ᵥ u) (t +ᵥ v) ↔ (⊥).Adj u v` is trivially
`False ↔ False`. -/
instance isTranslationInvariant_bot
    (T : Type u) [AddGroup T]
    (V : Type v) [AddAction T V] :
    IsTranslationInvariant T (⊥ : SimpleGraph V) where
  adj_vadd := by
    intro _ _ _
    simp [SimpleGraph.bot_adj]

/-- **Complete graph is translation invariant**: `(⊤ : SimpleGraph V)`
has an edge between every pair of distinct vertices, and distinctness
is preserved by translation (translations are always injective on
the ambient vertex type via the cancellation of the `AddAction`). -/
instance isTranslationInvariant_top
    (T : Type u) [AddGroup T]
    (V : Type v) [AddAction T V] :
    IsTranslationInvariant T (⊤ : SimpleGraph V) where
  adj_vadd := by
    intro t u v
    simp only [SimpleGraph.top_adj, ne_eq]
    refine ⟨fun h heq => h (by rw [heq]), fun h heq => ?_⟩
    apply h
    have := congrArg (fun x : V => (-t) +ᵥ x) heq
    simpa [add_vadd, neg_add_cancel, zero_vadd] using this

end Ambient

end IsingModel
