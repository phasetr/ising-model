import IsingModel.AmbientLattice
import IsingModel.AmbientLatticeSum

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
def vaddFinset {T : Type u} [AddGroup T] {V : Type v}
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

/-- **Identity translation is identity on Finset**:
`vaddFinset 0 A = A`. -/
@[simp]
theorem vaddFinset_zero {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V] (A : Finset V) :
    vaddFinset (0 : T) A = A := by
  unfold vaddFinset
  ext v
  simp [zero_vadd]

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

/-- **Subtype bijection between `↑Λ` and `↑(t +ᵥ Λ)`**: the natural
translation-induced bijection, sending `⟨v, hv⟩ : ↑Λ` to
`⟨t +ᵥ v, _⟩ : ↑(vaddFinset t Λ)` and vice versa via `-t`.

This is the structural datum underlying partition-function
translation invariance: summing over configurations of `↑Λ` and
of `↑(t +ᵥ Λ)` yield the same value after the identification. -/
def vaddSubtypeEquiv {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (t : T) (Λ : Finset V) :
    (↑Λ : Type _) ≃ (↑(vaddFinset t Λ) : Type _) where
  toFun := fun ⟨v, hv⟩ =>
    ⟨t +ᵥ v, by
      rw [mem_vaddFinset]
      exact ⟨v, hv, rfl⟩⟩
  invFun := fun ⟨v, hv⟩ =>
    ⟨(-t) +ᵥ v, by
      rw [mem_vaddFinset] at hv
      obtain ⟨u, huΛ, heq⟩ := hv
      have : (-t) +ᵥ v = u := by
        rw [← heq, ← add_vadd, neg_add_cancel, zero_vadd]
      rw [this]
      exact huΛ⟩
  left_inv := by
    rintro ⟨v, hv⟩
    apply Subtype.ext
    change (-t) +ᵥ (t +ᵥ v) = v
    rw [← add_vadd, neg_add_cancel, zero_vadd]
  right_inv := by
    rintro ⟨v, hv⟩
    apply Subtype.ext
    change t +ᵥ ((-t) +ᵥ v) = v
    rw [← add_vadd, add_neg_cancel, zero_vadd]

/-- **`vaddSubtypeEquiv` forward map unfolds to `t +ᵥ ·`**. -/
@[simp]
theorem vaddSubtypeEquiv_apply_coe {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (t : T) (Λ : Finset V) (x : (↑Λ : Type _)) :
    ((vaddSubtypeEquiv t Λ) x : V) = t +ᵥ (x : V) := by
  rfl

/-! ## Translation-invariant exhaustions

An exhaustion whose consecutive volumes differ by a disjoint
translate of the base block `volume 1` gives automatic
cardinality additivity `|Λ.volume (m + n)| = |Λ.volume m| +
|Λ.volume n|`, discharging the first field of
`DisjointTowerHypotheses`.

Deriving the second structural field, `super`, requires
translation-invariance of the Ising Hamiltonian itself and is
left to a subsequent PR. -/

/-- A **translation-invariant exhaustion** is an `Exhaustion V`
whose consecutive volumes differ by a disjoint translate of the
base block. `shift n : T` is the translation vector inserted at
stage `n+1`.

Informally: `Λ.volume 0 = ∅`, then `Λ.volume n` is built up by
successively adjoining disjoint translates of `Λ.volume 1`.
This is the natural structure under which Prop 4.6.1's
`hcard_add` hypothesis becomes automatic.

The field `shift_zero : shift 0 = 0` ensures the `n = 0` case of
`volume_succ` is self-consistent: it forces `volume 1 = volume 1`
(since `volume 0 = ∅` and `vaddFinset 0 (volume 1) = volume 1`
by `vaddFinset_zero`).

This structure concerns only the **exhaustion geometry**. It does
*not* by itself imply translation invariance of the graph edges
or of the Ising Hamiltonian — those are separate conditions.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.6 Prop 4.6.1,
p. 64. -/
structure TranslationInvariantExhaustion (T : Type u) [AddGroup T]
    (V : Type v) [DecidableEq V] [AddAction T V]
    extends Exhaustion V where
  /-- Translation vector inserted at the `n+1`-th stage. -/
  shift : ℕ → T
  /-- The stage-0 shift is the identity, making the `n = 0` case of
  `volume_succ` self-consistent (together with `volume_zero`). -/
  shift_zero : shift 0 = 0
  /-- `volume 0` is empty — the exhaustion starts from scratch. -/
  volume_zero : volume 0 = ∅
  /-- The `(n+1)`-th volume is the `n`-th volume together with the
  translated base block `shift n +ᵥ volume 1`. -/
  volume_succ : ∀ n,
    volume (n + 1) = volume n ∪ vaddFinset (shift n) (volume 1)
  /-- The translated base block is disjoint from `volume n`. -/
  disjoint_shift : ∀ n,
    Disjoint (volume n) (vaddFinset (shift n) (volume 1))

namespace TranslationInvariantExhaustion

variable {T : Type u} [AddGroup T] {V : Type v} [DecidableEq V]
  [AddAction T V]

/-- **Linear cardinality**: `|volume n| = n · |volume 1|` for any
translation-invariant exhaustion.

Proved by induction on `n`, using `volume_succ`,
`disjoint_shift`, and `vaddFinset_card`. -/
theorem volume_card_eq_mul
    (Λ : TranslationInvariantExhaustion T V) (n : ℕ) :
    (Λ.volume n).card = n * (Λ.volume 1).card := by
  induction n with
  | zero =>
    rw [Λ.volume_zero, Finset.card_empty, Nat.zero_mul]
  | succ n ih =>
    rw [Λ.volume_succ n,
        Finset.card_union_of_disjoint (Λ.disjoint_shift n),
        vaddFinset_card, ih]
    ring

/-- **`hcard_add` holds automatically**:
`|volume (m + n)| = |volume m| + |volume n|`. Direct from the
linear-cardinality formula. -/
theorem volume_card_add
    (Λ : TranslationInvariantExhaustion T V) (m n : ℕ) :
    (Λ.volume (m + n)).card = (Λ.volume m).card + (Λ.volume n).card := by
  rw [Λ.volume_card_eq_mul (m + n), Λ.volume_card_eq_mul m,
      Λ.volume_card_eq_mul n]
  ring

/-- **`DisjointTowerHypotheses` from a `TranslationInvariantExhaustion`
+ hypothesised `hsuper`**: given a translation-invariant exhaustion
(which handles `card_add` via `volume_card_add`) together with
user-supplied super-additivity of `log Z` and non-degeneracy
`(volume 1).card ≠ 0`, the full `DisjointTowerHypotheses` record
follows.

This is the abstract assembly step: the `hsuper` input itself —
`log Z_{volume m} + log Z_{volume n} ≤ log Z_{volume (m + n)}` —
is expected to come from a full translation-invariance proof of
the log partition function in a subsequent PR. Current step
provides the scaffold so that, once `hsuper` is derived, it
plugs directly into `freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.6 Prop 4.6.1,
p. 64. -/
def disjointTowerHypotheses_of_translationInvariant
    (Λ : TranslationInvariantExhaustion T V)
    (G : SimpleGraph V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hsuper : ∀ m n,
      Real.log (partitionFunctionΛ G (Λ.volume m) p)
        + Real.log (partitionFunctionΛ G (Λ.volume n) p)
        ≤ Real.log (partitionFunctionΛ G (Λ.volume (m + n)) p))
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    DisjointTowerHypotheses G Λ.toExhaustion p where
  card_add := Λ.volume_card_add
  super := hsuper
  card_one := hcard_one

/-- **Fekete convergence from a `TranslationInvariantExhaustion`**:
given a translation-invariant exhaustion, a bounded-edge-density
hypothesis, user-supplied `log Z` super-additivity `hsuper`, and
non-degenerate base step `hcard_one`, the exhaustion free-energy
density tends (in the sense of `Filter.Tendsto` at `Filter.atTop`)
to the infinite-volume free energy: `freeEnergyAlongExhaustion
G Λ.toExhaustion p` converges to `freeEnergyInfinite G
Λ.toExhaustion p`.

Thin wrapper over
`freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses`
(PR #204) + `disjointTowerHypotheses_of_translationInvariant`
(step 4 / PR #223). `card_add` is supplied automatically by the
exhaustion structure; once `hsuper` is derived from full
translation invariance (subsequent PR), this theorem will become
an unconditional-in-`hsuper` corollary.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.6 Prop 4.6.1,
p. 64. -/
theorem freeEnergyAlongExhaustion_tendsto_of_translationInvariant
    (Λ : TranslationInvariantExhaustion T V)
    (G : SimpleGraph V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ.toExhaustion)
    (hsuper : ∀ m n,
      Real.log (partitionFunctionΛ G (Λ.volume m) p)
        + Real.log (partitionFunctionΛ G (Λ.volume n) p)
        ≤ Real.log (partitionFunctionΛ G (Λ.volume (m + n)) p))
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto (freeEnergyAlongExhaustion G Λ.toExhaustion p)
      Filter.atTop
      (nhds (freeEnergyInfinite G Λ.toExhaustion p)) :=
  freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses G
    Λ.toExhaustion p hBED
    (disjointTowerHypotheses_of_translationInvariant Λ G p
      hsuper hcard_one)

end TranslationInvariantExhaustion

end Ambient

end IsingModel
