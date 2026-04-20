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

/-! ## Translated Finset API

Translating a `Finset V` by `t : T` gives another `Finset V` with the
same cardinality (translations are injective on `V` via cancellation
in the `AddAction` on an `AddGroup`). These are the elementary
facts needed for the next step toward `DisjointTowerHypotheses`
under translation invariance. -/

/-- **Translation is injective on `V`**: `t +ᵥ u = t +ᵥ v ↔ u = v`
for any `t : T` and `u, v : V`, via cancellation in the `AddAction`
on an `AddGroup` (applying `(-t) +ᵥ ·` to both sides). -/
theorem vadd_injective {T : Type u} [AddGroup T] {V : Type v}
    [AddAction T V] (t : T) :
    Function.Injective (t +ᵥ · : V → V) := by
  intro u v heq
  have : (-t) +ᵥ (t +ᵥ u) = (-t) +ᵥ (t +ᵥ v) := congrArg _ heq
  simpa [← add_vadd, neg_add_cancel, zero_vadd] using this

/-- **Translated Finset**: `t +ᵥ A := A.image (t +ᵥ ·)`; a `Finset V`
obtained by translating every element of `A` by `t`. -/
noncomputable def vaddFinset {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (t : T) (A : Finset V) : Finset V :=
  A.image (t +ᵥ ·)

/-- **Cardinality is preserved by translation**:
`(t +ᵥ A).card = A.card`, via injectivity of translation. -/
@[simp]
theorem vaddFinset_card {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (t : T) (A : Finset V) :
    (vaddFinset t A).card = A.card := by
  unfold vaddFinset
  exact Finset.card_image_of_injective _ (vadd_injective t)

/-- **Membership in a translated Finset**: `v ∈ t +ᵥ A ↔ ∃ u ∈ A, t +ᵥ u = v`. -/
theorem mem_vaddFinset {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (t : T) (A : Finset V) (v : V) :
    v ∈ vaddFinset t A ↔ ∃ u ∈ A, t +ᵥ u = v := by
  unfold vaddFinset
  simp [Finset.mem_image]

/-- **Disjointness is preserved by translation**:
if `A` and `B` are disjoint as `Finset V`, then `t +ᵥ A` and
`t +ᵥ B` are also disjoint.

Proof: if `v ∈ (t +ᵥ A) ∩ (t +ᵥ B)` then `v = t +ᵥ u₁ = t +ᵥ u₂`
for some `u₁ ∈ A`, `u₂ ∈ B`; by `vadd_injective`, `u₁ = u₂`, so
`u₁ ∈ A ∩ B`, contradicting disjointness. -/
theorem vaddFinset_disjoint_of_disjoint {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (t : T) {A B : Finset V} (h : Disjoint A B) :
    Disjoint (vaddFinset t A) (vaddFinset t B) := by
  rw [Finset.disjoint_left]
  intro v hvA hvB
  rw [mem_vaddFinset] at hvA hvB
  obtain ⟨u₁, hu₁A, heq₁⟩ := hvA
  obtain ⟨u₂, hu₂B, heq₂⟩ := hvB
  have hu_eq : u₁ = u₂ := vadd_injective t (heq₁.trans heq₂.symm)
  subst hu_eq
  exact Finset.disjoint_left.mp h hu₁A hu₂B

end Ambient

end IsingModel
