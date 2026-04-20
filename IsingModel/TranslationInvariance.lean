import IsingModel.AmbientLattice
import IsingModel.AmbientLatticeSum
import IsingModel.Hamiltonian

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
  Point of View*, 2nd ed., Springer 1987, §4.6 Prop 4.6.1, p. 68.
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
(GJ §4.6 Prop 4.6.1 p. 68). The translation-invariance-driven
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

/-- **Translation distributes over union**:
`vaddFinset t (A ∪ B) = vaddFinset t A ∪ vaddFinset t B`. -/
theorem vaddFinset_union {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V] (t : T) (A B : Finset V) :
    vaddFinset t (A ∪ B) = vaddFinset t A ∪ vaddFinset t B := by
  unfold vaddFinset
  exact Finset.image_union _ _

/-- **Translation distributes over empty Finset**: `vaddFinset t ∅ = ∅`. -/
@[simp]
theorem vaddFinset_empty {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V] (t : T) :
    vaddFinset t (∅ : Finset V) = ∅ := by
  unfold vaddFinset
  exact Finset.image_empty _

/-- **Translations compose additively**:
`vaddFinset s (vaddFinset t A) = vaddFinset (s + t) A`. -/
theorem vaddFinset_add {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V] (s t : T) (A : Finset V) :
    vaddFinset s (vaddFinset t A) = vaddFinset (s + t) A := by
  unfold vaddFinset
  rw [Finset.image_image]
  congr 1
  ext v
  exact (add_vadd s t v).symm

/-! ## Shifted exhaustions -/

/-- **Shifted exhaustion** `Λ.shift t : Ambient.Exhaustion V` whose
stage-`n` volume is the translated Finset `vaddFinset t (Λ.volume n)`.

Monotonicity is pointwise (via `Finset.image_mono` encoded through
`vaddFinset`), and the exhaust property transfers: any finite
`A : Finset V` has `A = vaddFinset t (vaddFinset (-t) A)`, and
`vaddFinset (-t) A` is eventually covered by `Λ.volume n`, hence
`A ⊆ (Λ.shift t).volume n` for large `n`.

Infrastructure for translation-invariance lifts of
`correlationInfinite`, `freeEnergyInfinite`, etc.: composing with
exhaustion-independence (`correlationInfinite G Λ = correlationInfinite
G Λ'`) lets us replace the reference exhaustion without altering
the value. -/
def Exhaustion.shift {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (Λ : Exhaustion V) (t : T) : Exhaustion V where
  volume n := vaddFinset t (Λ.volume n)
  mono := by
    intro m n hmn x hx
    rw [mem_vaddFinset] at hx ⊢
    obtain ⟨u, huΛm, heq⟩ := hx
    exact ⟨u, Λ.mono hmn huΛm, heq⟩
  exhaust := by
    intro A
    obtain ⟨N, hN⟩ := Λ.exhaust (vaddFinset (-t) A)
    refine ⟨N, ?_⟩
    intro n hn x hxA
    rw [mem_vaddFinset]
    have hx' : (-t) +ᵥ x ∈ vaddFinset (-t) A := by
      rw [mem_vaddFinset]
      exact ⟨x, hxA, rfl⟩
    have : (-t) +ᵥ x ∈ Λ.volume n := hN n hn hx'
    refine ⟨(-t) +ᵥ x, this, ?_⟩
    have : t +ᵥ ((-t) +ᵥ x) = x := by
      rw [← add_vadd, add_neg_cancel, zero_vadd]
    exact this

/-- **Stage-`n` volume of `Λ.shift t`** is `vaddFinset t (Λ.volume n)`
(definitional `simp` lemma). -/
@[simp]
theorem Exhaustion.shift_volume {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (Λ : Exhaustion V) (t : T) (n : ℕ) :
    (Λ.shift t).volume n = vaddFinset t (Λ.volume n) := rfl

/-- **Cardinality preservation under shift**:
`|(Λ.shift t).volume n| = |Λ.volume n|` for every `n`. -/
@[simp]
theorem Exhaustion.shift_volume_card {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (Λ : Exhaustion V) (t : T) (n : ℕ) :
    ((Λ.shift t).volume n).card = (Λ.volume n).card := by
  rw [Exhaustion.shift_volume, vaddFinset_card]

/-- **Shifting by `0` is identity on volumes**:
`(Λ.shift 0).volume n = Λ.volume n`. -/
@[simp]
theorem Exhaustion.shift_zero_volume {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (Λ : Exhaustion V) (n : ℕ) :
    (Λ.shift (0 : T)).volume n = Λ.volume n := by
  rw [Exhaustion.shift_volume, vaddFinset_zero]

/-- **Structure-level identity**: `Λ.shift 0 = Λ` as `Exhaustion V`.
Consequence of `shift_zero_volume` via extensionality on `volume`;
`Exhaustion` is a one-field structure modulo `Prop`-valued
`mono` / `exhaust`. -/
@[simp]
theorem Exhaustion.shift_zero {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (Λ : Exhaustion V) :
    Λ.shift (0 : T) = Λ := by
  cases Λ
  simp only [Exhaustion.shift, Exhaustion.mk.injEq]
  funext n
  simp [vaddFinset_zero]

/-- **Composition of shifts**: `(Λ.shift t).shift s = Λ.shift (s + t)`
at the volume level, via `vaddFinset_add`. -/
@[simp]
theorem Exhaustion.shift_shift_volume {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (Λ : Exhaustion V) (s t : T) (n : ℕ) :
    ((Λ.shift t).shift s).volume n = (Λ.shift (s + t)).volume n := by
  simp [Exhaustion.shift_volume, vaddFinset_add]

/-- **Inverse shift cancels**: `(Λ.shift t).shift (-t) = Λ`
at the volume level. -/
@[simp]
theorem Exhaustion.shift_neg_shift_volume {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (Λ : Exhaustion V) (t : T) (n : ℕ) :
    ((Λ.shift t).shift (-t)).volume n = Λ.volume n := by
  rw [Exhaustion.shift_shift_volume, neg_add_cancel, Exhaustion.shift_zero_volume]

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

/-- **Induced-graph adjacency is preserved by translation**: when
`G : SimpleGraph V` is translation invariant under an `AddAction T V`
and `Λ : Finset V`, the induced adjacency on the translated Finset
matches that on the original via `vaddSubtypeEquiv`:

`(inducedGraph G (vaddFinset t Λ)).Adj (vaddSubtypeEquiv t Λ u)
  (vaddSubtypeEquiv t Λ v) ↔ (inducedGraph G Λ).Adj u v`.

Proof: both sides unfold to `G.Adj (·) (·)` on raw vertex values;
on the LHS the raw values are `t +ᵥ u.val` and `t +ᵥ v.val`,
and `IsTranslationInvariant.adj_vadd` converts to the RHS. -/
theorem inducedGraph_vaddFinset_adj_iff {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (t : T) (Λ : Finset V) (u v : (↑Λ : Type _)) :
    (inducedGraph G (vaddFinset t Λ)).Adj
        (vaddSubtypeEquiv t Λ u) (vaddSubtypeEquiv t Λ v)
      ↔ (inducedGraph G Λ).Adj u v := by
  unfold inducedGraph
  -- G.induce S.Adj x y = G.Adj x.val y.val definitionally.
  change G.Adj (((vaddSubtypeEquiv t Λ) u : V))
      ((vaddSubtypeEquiv t Λ v : V)) ↔ G.Adj (u : V) (v : V)
  rw [vaddSubtypeEquiv_apply_coe, vaddSubtypeEquiv_apply_coe]
  exact IsTranslationInvariant.adj_vadd t (u : V) (v : V)

/-- **Config-level translation equiv**:
`Config ↑Λ ≃ Config ↑(vaddFinset t Λ)`, obtained by pre-composing
spin configurations with `(vaddSubtypeEquiv t Λ).symm`.

Explicit directions:
- `configVaddEquiv t Λ σ = σ ∘ (vaddSubtypeEquiv t Λ).symm`.
- `(configVaddEquiv t Λ).symm σ' = σ' ∘ vaddSubtypeEquiv t Λ`.

This is the reindexing isomorphism used in the subsequent
partition-function translation-invariance step (rewrite
`∑_{σ' : Config ↑(vaddFinset t Λ)} f(σ')` as
`∑_{σ : Config ↑Λ} f(configVaddEquiv t Λ σ)` via
`Fintype.sum_equiv`). -/
def configVaddEquiv {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (t : T) (Λ : Finset V) :
    Config (↑Λ : Type _) ≃ Config (↑(vaddFinset t Λ) : Type _) :=
  Equiv.arrowCongr (vaddSubtypeEquiv t Λ) (Equiv.refl Spin)

/-- **Action of `configVaddEquiv` on a point** (forward direction):
`(configVaddEquiv t Λ σ) j = σ ((vaddSubtypeEquiv t Λ).symm j)` for
`j : ↑(vaddFinset t Λ)`. Unfolding lemma for the `Equiv.arrowCongr`
construction. -/
@[simp]
theorem configVaddEquiv_apply {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (t : T) (Λ : Finset V) (σ : Config (↑Λ : Type _))
    (j : (↑(vaddFinset t Λ) : Type _)) :
    (configVaddEquiv t Λ σ) j = σ ((vaddSubtypeEquiv t Λ).symm j) := rfl

/-- **Action of `(configVaddEquiv t Λ).symm` on a point**:
`((configVaddEquiv t Λ).symm σ') i = σ' (vaddSubtypeEquiv t Λ i)` for
`i : ↑Λ`. Unfolding lemma for the inverse of the `Equiv.arrowCongr`. -/
@[simp]
theorem configVaddEquiv_symm_apply {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (t : T) (Λ : Finset V) (σ' : Config (↑(vaddFinset t Λ) : Type _))
    (i : (↑Λ : Type _)) :
    ((configVaddEquiv t Λ).symm σ') i = σ' (vaddSubtypeEquiv t Λ i) := rfl

/-- **`externalFieldEnergy` is invariant under `configVaddEquiv`**:
for any translation `t : T` and any `Λ : Finset V`,

`externalFieldEnergy h σ' = externalFieldEnergy h
  ((configVaddEquiv t Λ).symm σ')`

where `σ' : Config ↑(vaddFinset t Λ)`.

Proof: `externalFieldEnergy h σ = -h * ∑_i Spin.sign ℝ (σ i)`;
the sum `∑_{i : ↑(vaddFinset t Λ)} Spin.sign ℝ (σ' i)` reindexes
via `Fintype.sum_equiv (vaddSubtypeEquiv t Λ)` to
`∑_{j : ↑Λ} Spin.sign ℝ (σ' (vaddSubtypeEquiv t Λ j))`, and the
inner term equals `((configVaddEquiv t Λ).symm σ') j` definitionally
(by the definition of `Equiv.arrowCongr`, whose `.symm` applied to
`σ'` is exactly `σ' ∘ (vaddSubtypeEquiv t Λ)`). -/
theorem externalFieldEnergy_configVaddEquiv_symm {T : Type u}
    [AddGroup T] {V : Type v} [DecidableEq V] [AddAction T V]
    (t : T) (Λ : Finset V) (h : ℝ)
    (σ' : Config (↑(vaddFinset t Λ) : Type _)) :
    IsingModel.externalFieldEnergy h σ'
      = IsingModel.externalFieldEnergy h
          ((configVaddEquiv t Λ).symm σ') := by
  unfold IsingModel.externalFieldEnergy
  congr 1
  symm
  exact Fintype.sum_equiv (vaddSubtypeEquiv t Λ)
      (fun j => Spin.sign ℝ (((configVaddEquiv t Λ).symm σ') j))
      (fun i => Spin.sign ℝ (σ' i))
      (fun _ => rfl)

/-- **Induced-graph translation isomorphism**: for a translation-
invariant graph `G` and a translate `vaddFinset t Λ`, the induced
graphs are isomorphic via `(vaddSubtypeEquiv t Λ).symm` (as a
graph isomorphism `≃g`).

`map_rel_iff'` uses `inducedGraph_vaddFinset_adj_iff` (PR #227);
the underlying equivalence is the inverse of `vaddSubtypeEquiv`
so the direction matches `RelIso`'s convention.

Intended use: pull back sums over edges of
`inducedGraph G (vaddFinset t Λ)` to sums over edges of
`inducedGraph G Λ` via the induced `mapEdgeSet` equivalence, in
the subsequent step deriving translation-invariance of
`interactionEnergy` / `partitionFunctionΛ`. -/
def inducedGraphVaddIso {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (t : T) (Λ : Finset V) :
    inducedGraph G (vaddFinset t Λ) ≃g inducedGraph G Λ where
  toEquiv := (vaddSubtypeEquiv t Λ).symm
  map_rel_iff' := by
    intro u v
    -- Goal:
    --   (inducedGraph G Λ).Adj
    --       ((vaddSubtypeEquiv t Λ).symm u)
    --       ((vaddSubtypeEquiv t Λ).symm v)
    --     ↔ (inducedGraph G (vaddFinset t Λ)).Adj u v
    have := inducedGraph_vaddFinset_adj_iff G t Λ
              ((vaddSubtypeEquiv t Λ).symm u)
              ((vaddSubtypeEquiv t Λ).symm v)
    simp only [Equiv.apply_symm_apply] at this
    exact this.symm

/-- **`edgeSpin` compatibility with `Sym2.map (vaddSubtypeEquiv)`**:
for any `σ' : Config ↑(vaddFinset t Λ)` and any `e : Sym2 ↑Λ`,

`edgeSpin σ' (Sym2.map (vaddSubtypeEquiv t Λ) e)
  = edgeSpin ((configVaddEquiv t Λ).symm σ') e`.

Reading right-to-left: evaluating `σ := σ' ∘ vaddSubtypeEquiv` on
the untranslated edge `e` equals evaluating the original `σ'` on
the translated edge `Sym2.map vaddSubtypeEquiv e`.

Proof by `Sym2.ind` + definitional unfolding of `Sym2.lift`/
`Sym2.map`/`Equiv.arrowCongr`. -/
theorem edgeSpin_map_vaddSubtypeEquiv {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (t : T) (Λ : Finset V)
    (σ' : Config (↑(vaddFinset t Λ) : Type _))
    (e : Sym2 (↑Λ : Type _)) :
    (IsingModel.edgeSpin σ'
        (Sym2.map (vaddSubtypeEquiv t Λ) e) : ℝ)
      = IsingModel.edgeSpin
          ((configVaddEquiv t Λ).symm σ') e := by
  refine Sym2.ind (fun _ _ => ?_) e
  rfl

/-- **`interactionEnergy` is invariant under `configVaddEquiv`**:
for a translation-invariant graph `G` and any `Λ : Finset V`,

`interactionEnergy (inducedGraph G (vaddFinset t Λ)) J σ'
  = interactionEnergy (inducedGraph G Λ) J ((configVaddEquiv t Λ).symm σ')`.

Proof: unfold to the sum over edges; rewrite using
`Finset.sum_nbij'` with `i := Sym2.map (vaddSubtypeEquiv t Λ).symm`
and inverse `j := Sym2.map (vaddSubtypeEquiv t Λ)`. Membership
preservation comes from the graph iso `inducedGraphVaddIso`
(step 6e) applied at the `SimpleGraph.Hom.map_mem_edgeSet` level;
per-edge equality follows from `edgeSpin_map_vaddSubtypeEquiv`. -/
theorem interactionEnergy_configVaddEquiv_symm {T : Type u}
    [AddGroup T] {V : Type v} [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (t : T) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    [Fintype (inducedGraph G (vaddFinset t Λ)).edgeSet]
    (J : ℝ) (σ' : Config (↑(vaddFinset t Λ) : Type _)) :
    IsingModel.interactionEnergy (inducedGraph G (vaddFinset t Λ)) J σ'
      = IsingModel.interactionEnergy (inducedGraph G Λ) J
          ((configVaddEquiv t Λ).symm σ') := by
  unfold IsingModel.interactionEnergy
  congr 1
  -- Direct proof via Finset.sum_nbij' with explicit (vaddSubtypeEquiv t Λ).symm
  -- as the forward map on Sym2 (from G₁-edges to G₂-edges).
  refine Finset.sum_nbij'
    (fun e => Sym2.map (vaddSubtypeEquiv t Λ).symm e)
    (fun e' => Sym2.map (vaddSubtypeEquiv t Λ) e') ?_ ?_ ?_ ?_ ?_
  · -- hi: maps edges of G₁ to edges of G₂ via the iso
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact (inducedGraphVaddIso G t Λ).toEmbedding.toHom.map_mem_edgeSet he
  · -- hj: inverse direction via the symm iso
    intro e' he'
    rw [SimpleGraph.mem_edgeFinset] at he' ⊢
    change Sym2.map (vaddSubtypeEquiv t Λ) e' ∈
      (inducedGraph G (vaddFinset t Λ)).edgeSet
    exact (inducedGraphVaddIso G t Λ).symm.toEmbedding.toHom.map_mem_edgeSet he'
  · -- left_inv: j (i e) = e on ι = Sym2 ↑(vaddFinset t Λ)
    intro e _
    change Sym2.map (vaddSubtypeEquiv t Λ)
          (Sym2.map (vaddSubtypeEquiv t Λ).symm e) = e
    rw [Sym2.map_map]
    simp
  · -- right_inv: i (j e') = e' on κ = Sym2 ↑Λ
    intro e' _
    change Sym2.map (vaddSubtypeEquiv t Λ).symm
          (Sym2.map (vaddSubtypeEquiv t Λ) e') = e'
    rw [Sym2.map_map]
    simp
  · -- h: edgeSpin σ' e = edgeSpin (symm σ') (Sym2.map symm e)
    intro e _
    -- Use edgeSpin_map_vaddSubtypeEquiv with e'' := Sym2.map (symm) e; then
    -- LHS goal becomes edgeSpin σ' (Sym2.map eq (Sym2.map symm e))
    -- which equals edgeSpin σ' e by Sym2.map_map + apply_symm_apply.
    have hidentity : e = Sym2.map (vaddSubtypeEquiv t Λ)
        (Sym2.map (vaddSubtypeEquiv t Λ).symm e) := by
      rw [Sym2.map_map]; simp
    conv_lhs => rw [hidentity]
    exact edgeSpin_map_vaddSubtypeEquiv t Λ σ'
      (Sym2.map (vaddSubtypeEquiv t Λ).symm e)

/-- **Hamiltonian equivariance under `configVaddEquiv`**: combine
interaction (step 6f) + external-field (step 6d) energies. -/
theorem hamiltonian_configVaddEquiv_symm {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (t : T) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    [Fintype (inducedGraph G (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ)
    (σ' : Config (↑(vaddFinset t Λ) : Type _)) :
    IsingModel.hamiltonian (inducedGraph G (vaddFinset t Λ)) p σ'
      = IsingModel.hamiltonian (inducedGraph G Λ) p
          ((configVaddEquiv t Λ).symm σ') := by
  unfold IsingModel.hamiltonian
  rw [interactionEnergy_configVaddEquiv_symm G t Λ p.J σ',
      externalFieldEnergy_configVaddEquiv_symm t Λ p.h σ']

/-- **`partitionFunctionΛ` is translation invariant**: for a
translation-invariant graph `G` and `Λ : Finset V`,

`partitionFunctionΛ G (vaddFinset t Λ) p = partitionFunctionΛ G Λ p`.

Proof: unfold both sides to sums over Config of the respective
Finsets, then reindex via `Fintype.sum_equiv (configVaddEquiv t Λ).symm`
(thus mapping σ' on ↑(vaddFinset t Λ) to σ := (symm) σ' on ↑Λ), and
use Hamiltonian equivariance to match summands. -/
theorem partitionFunctionΛ_vaddFinset_eq {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (t : T) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    [Fintype (inducedGraph G (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) :
    partitionFunctionΛ G (vaddFinset t Λ) p
      = partitionFunctionΛ G Λ p := by
  change IsingModel.partitionFunction
      (inducedGraph G (vaddFinset t Λ)) p
    = IsingModel.partitionFunction (inducedGraph G Λ) p
  unfold IsingModel.partitionFunction IsingModel.boltzmannWeight
  -- Reindex ∑_{σ'} over Config ↑(t +ᵥ Λ) to ∑_σ over Config ↑Λ.
  refine (Fintype.sum_equiv (configVaddEquiv t Λ)
    (fun σ => Real.exp (-p.β *
        IsingModel.hamiltonian (inducedGraph G Λ) p σ))
    (fun σ' => Real.exp (-p.β *
        IsingModel.hamiltonian (inducedGraph G (vaddFinset t Λ)) p σ'))
    ?_).symm
  intro σ
  -- Want: exp(-β H_Λ σ) = exp(-β H_{t+Λ} ((configVaddEquiv) σ)).
  change Real.exp (-p.β *
        IsingModel.hamiltonian (inducedGraph G Λ) p σ)
      = Real.exp (-p.β *
        IsingModel.hamiltonian (inducedGraph G (vaddFinset t Λ)) p
            ((configVaddEquiv t Λ) σ))
  rw [hamiltonian_configVaddEquiv_symm G t Λ p (configVaddEquiv t Λ σ),
      Equiv.symm_apply_apply]

/-- **Spin product equivariance under `configVaddEquiv`**:
for `A : Finset ↑Λ`, `σ : Config ↑Λ`, and translation `t : T`,

`spinProduct (A.map (vaddSubtypeEquiv t Λ).toEmbedding)
  (configVaddEquiv t Λ σ) = spinProduct A σ`.

The image Finset `A.map (vaddSubtypeEquiv t Λ).toEmbedding` is the
translated set of sites inside `↑(vaddFinset t Λ)`. Reindexing the
`∏_j toSign((configVaddEquiv σ) j)` product via `Finset.prod_map`
reduces to `∏_i toSign((configVaddEquiv σ) (emb i)) = ∏_i toSign(σ i)`,
since `configVaddEquiv t Λ σ = σ ∘ (vaddSubtypeEquiv t Λ).symm` and
`emb = (vaddSubtypeEquiv t Λ).toEmbedding`. -/
theorem spinProduct_map_configVaddEquiv {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (t : T) (Λ : Finset V) (A : Finset (↑Λ : Type _))
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.spinProduct (A.map (vaddSubtypeEquiv t Λ).toEmbedding)
        (configVaddEquiv t Λ σ)
      = IsingModel.spinProduct A σ := by
  unfold IsingModel.spinProduct
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro i _
  -- `configVaddEquiv t Λ σ = σ ∘ (vaddSubtypeEquiv t Λ).symm`, so at
  -- `emb i = vaddSubtypeEquiv t Λ i` we get `σ ((vaddSubtypeEquiv ...).symm
  -- ((vaddSubtypeEquiv ...) i)) = σ i`.
  have h : configVaddEquiv t Λ σ (vaddSubtypeEquiv t Λ i) = σ i := by
    simp
  -- Goal: `↑((configVaddEquiv t Λ σ) ((vaddSubtypeEquiv t Λ).toEmbedding i)).toSign
  --        = ↑(σ i).toSign` (cast into ℝ).
  change (↑((configVaddEquiv t Λ σ)
      (vaddSubtypeEquiv t Λ i)).toSign : ℝ) = (↑(σ i).toSign : ℝ)
  rw [h]

/-- **Correlation equivariance under ambient translation**: for a
translation-invariant graph `G` and any `A : Finset ↑Λ`,

`correlationΛ G (vaddFinset t Λ) p (A.map (vaddSubtypeEquiv t Λ).toEmbedding)
  = correlationΛ G Λ p A`.

Composes `partitionFunctionΛ_vaddFinset_eq` (denominator) with
`hamiltonian_configVaddEquiv_symm` + `spinProduct_map_configVaddEquiv`
(numerator) via `configVaddEquiv` reindexing. -/
theorem correlationΛ_vaddFinset_eq {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (t : T) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    [Fintype (inducedGraph G (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) (A : Finset (↑Λ : Type _)) :
    correlationΛ G (vaddFinset t Λ) p
        (A.map (vaddSubtypeEquiv t Λ).toEmbedding)
      = correlationΛ G Λ p A := by
  -- Unfold `correlationΛ = IsingModel.correlation = gibbsExpectation (spinProduct _)`.
  change IsingModel.correlation (inducedGraph G (vaddFinset t Λ)) p
      (A.map (vaddSubtypeEquiv t Λ).toEmbedding)
    = IsingModel.correlation (inducedGraph G Λ) p A
  unfold IsingModel.correlation IsingModel.gibbsExpectation
  -- The partition function factors are equal by `partitionFunctionΛ_vaddFinset_eq`.
  have hZ : IsingModel.partitionFunction (inducedGraph G (vaddFinset t Λ)) p
      = IsingModel.partitionFunction (inducedGraph G Λ) p := by
    change partitionFunctionΛ G (vaddFinset t Λ) p = partitionFunctionΛ G Λ p
    exact partitionFunctionΛ_vaddFinset_eq G t Λ p
  rw [hZ]
  congr 1
  -- Reindex ∑_{σ'} over Config ↑(vaddFinset t Λ) to ∑_σ over Config ↑Λ.
  refine (Fintype.sum_equiv (configVaddEquiv t Λ)
    (fun σ => IsingModel.spinProduct A σ
        * IsingModel.boltzmannWeight (inducedGraph G Λ) p σ)
    (fun σ' => IsingModel.spinProduct
        (A.map (vaddSubtypeEquiv t Λ).toEmbedding) σ'
      * IsingModel.boltzmannWeight (inducedGraph G (vaddFinset t Λ)) p σ')
    ?_).symm
  intro σ
  -- Both factors equal under `configVaddEquiv`:
  -- spinProduct via `spinProduct_map_configVaddEquiv`,
  -- boltzmannWeight via `hamiltonian_configVaddEquiv_symm`.
  have h_sp := spinProduct_map_configVaddEquiv t Λ A σ
  have h_bw : IsingModel.boltzmannWeight (inducedGraph G Λ) p σ
      = IsingModel.boltzmannWeight (inducedGraph G (vaddFinset t Λ)) p
          (configVaddEquiv t Λ σ) := by
    unfold IsingModel.boltzmannWeight
    rw [hamiltonian_configVaddEquiv_symm G t Λ p (configVaddEquiv t Λ σ),
        Equiv.symm_apply_apply]
  simp only [h_bw, h_sp]

/-- **Subset transport under translation**: `A ⊆ Λ` is equivalent to
`vaddFinset t A ⊆ vaddFinset t Λ`, via injectivity of the translate. -/
theorem vaddFinset_subset_iff {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V] (t : T) (A Λ : Finset V) :
    vaddFinset t A ⊆ vaddFinset t Λ ↔ A ⊆ Λ := by
  refine ⟨fun h x hxA => ?_, fun h x hx => ?_⟩
  · -- `x ∈ A` ⇒ `t +ᵥ x ∈ vaddFinset t A ⊆ vaddFinset t Λ` ⇒ `x ∈ Λ`.
    have : t +ᵥ x ∈ vaddFinset t A :=
      (mem_vaddFinset t A (t +ᵥ x)).mpr ⟨x, hxA, rfl⟩
    have := h this
    rw [mem_vaddFinset] at this
    obtain ⟨u, huΛ, heq⟩ := this
    have : u = x := vadd_injective t heq
    exact this ▸ huΛ
  · rw [mem_vaddFinset] at hx
    obtain ⟨u, huA, heq⟩ := hx
    rw [← heq, mem_vaddFinset]
    exact ⟨u, h huA, rfl⟩

/-- **Image of `liftFinset` under `vaddSubtypeEquiv`**: for `A ⊆ Λ`,
`liftFinset (vaddFinset t A) _` in `↑(vaddFinset t Λ)` equals the
image of `liftFinset A hA` in `↑Λ` under the translation bijection.

This bridges the volume-translation identity `partitionFunctionΛ_vaddFinset_eq`
and its correlation counterpart with the along-exhaustion framework. -/
theorem liftFinset_vaddFinset_eq {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (t : T) {Λ : Finset V} {A : Finset V} (hA : A ⊆ Λ) :
    liftFinset (vaddFinset t A)
        ((vaddFinset_subset_iff t A Λ).mpr hA)
      = (liftFinset A hA).map (vaddSubtypeEquiv t Λ).toEmbedding := by
  ext x
  rw [mem_liftFinset, Finset.mem_map]
  simp only [Equiv.coe_toEmbedding]
  refine ⟨fun hx => ?_, ?_⟩
  · -- `x : ↑(vaddFinset t Λ)`, `x.val ∈ vaddFinset t A`.
    rw [mem_vaddFinset] at hx
    obtain ⟨u, huA, heq⟩ := hx
    refine ⟨⟨u, hA huA⟩, ?_, ?_⟩
    · rw [mem_liftFinset]; exact huA
    · -- `vaddSubtypeEquiv t Λ ⟨u, hA huA⟩ = ⟨t + u, _⟩ = x`.
      apply Subtype.ext
      change t +ᵥ u = x.val
      exact heq
  · rintro ⟨⟨u, huΛ⟩, huA, hxeq⟩
    rw [mem_liftFinset] at huA
    -- `vaddSubtypeEquiv t Λ ⟨u, huΛ⟩ = ⟨t + u, _⟩`.
    have hxval : x.val = t +ᵥ u := by
      have : x = vaddSubtypeEquiv t Λ ⟨u, huΛ⟩ := hxeq.symm
      rw [this]
      rfl
    rw [hxval, mem_vaddFinset]
    exact ⟨u, huA, rfl⟩

/-- **Translation invariance of `correlationAlongExhaustion` via
`Exhaustion.shift`**: under `IsTranslationInvariant T G`, for every `n`,

`correlationAlongExhaustion G (Λ.shift t) p (vaddFinset t A) n
  = correlationAlongExhaustion G Λ p A n`.

Proof: the subset condition is equivalent by `vaddFinset_subset_iff`;
when both hold, `liftFinset_vaddFinset_eq` + `correlationΛ_vaddFinset_eq`
reduce to `correlationΛ G (Λ.volume n) p (liftFinset A _)`. Both sides
are `0` when the subset condition fails. -/
theorem correlationAlongExhaustion_shift_vaddFinset_eq
    {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (Λ : Exhaustion V) (t : T)
    [hF1 : ∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [hF2 : ∀ n, Fintype (inducedGraph G ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) (n : ℕ) :
    correlationAlongExhaustion G (Λ.shift t) p (vaddFinset t A) n
      = correlationAlongExhaustion G Λ p A n := by
  -- Note: the proof below relies on `(Λ.shift t).volume n` being
  -- definitionally equal to `vaddFinset t (Λ.volume n)` via the `shift`
  -- `volume` field equation. A refactor of `Exhaustion.shift` that breaks
  -- this reducibility would require explicit `Exhaustion.shift_volume`
  -- rewrites in the subset and term-construction steps.
  by_cases hA : A ⊆ Λ.volume n
  · -- Subset case.
    have hA' : vaddFinset t A ⊆ vaddFinset t (Λ.volume n) :=
      (vaddFinset_subset_iff t A (Λ.volume n)).mpr hA
    have hshiftA : vaddFinset t A ⊆ (Λ.shift t).volume n := hA'
    rw [correlationAlongExhaustion_of_subset G (Λ.shift t) p hshiftA,
        correlationAlongExhaustion_of_subset G Λ p hA]
    -- Now the goal is
    --   `correlationΛ G ((Λ.shift t).volume n) p (liftFinset (vaddFinset t A) hshiftA)
    --      = correlationΛ G (Λ.volume n) p (liftFinset A hA)`.
    -- The LHS's graph argument is definitionally `vaddFinset t (Λ.volume n)`.
    -- Invoke `correlationΛ_vaddFinset_eq` with the `hF2 n` Fintype to directly
    -- supply the equality.
    have key : @correlationΛ V _ G (vaddFinset t (Λ.volume n))
        (hF2 n) p ((liftFinset A hA).map (vaddSubtypeEquiv t (Λ.volume n)).toEmbedding)
      = correlationΛ G (Λ.volume n) p (liftFinset A hA) :=
      @correlationΛ_vaddFinset_eq _ _ _ _ _ G _ t (Λ.volume n) _ (hF2 n) p (liftFinset A hA)
    -- The LHS's lifted Finset is `liftFinset (vaddFinset t A) hshiftA` and, since
    -- `hshiftA` is defEq to `hA'`, equals `(liftFinset A hA).map emb` via
    -- `liftFinset_vaddFinset_eq`.
    rw [show liftFinset (vaddFinset t A) hshiftA
        = (liftFinset A hA).map (vaddSubtypeEquiv t (Λ.volume n)).toEmbedding from
        liftFinset_vaddFinset_eq t hA]
    exact key
  · -- Not-subset case: both sides are `0`.
    have hA' : ¬ vaddFinset t A ⊆ (Λ.shift t).volume n := by
      change ¬ vaddFinset t A ⊆ vaddFinset t (Λ.volume n)
      rw [vaddFinset_subset_iff]
      exact hA
    rw [correlationAlongExhaustion_of_not_subset G (Λ.shift t) p hA',
        correlationAlongExhaustion_of_not_subset G Λ p hA]

set_option linter.unusedFintypeInType false in
/-- **Translation invariance of `correlationInfinite` under translation
of the observable**: for `IsTranslationInvariant T G`, ferromagnetic `p`,
any `t : T` and `A : Finset V`,

`correlationInfinite G Λ p (vaddFinset t A) = correlationInfinite G Λ p A`.

Proof: combine exhaustion-independence (Λ vs Λ.shift t, Ferromagnetic
hypothesis) with the per-stage shift identity
`correlationAlongExhaustion_shift_vaddFinset_eq`. -/
theorem correlationInfinite_vaddFinset_of_translationInvariant
    {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (Λ : Exhaustion V) (t : T)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset V) :
    correlationInfinite G Λ p (vaddFinset t A)
      = correlationInfinite G Λ p A := by
  -- Step 1: Exhaustion independence — replace `Λ` by `Λ.shift t`.
  rw [correlationInfinite_indep_exhaustion G Λ (Λ.shift t) p hf (vaddFinset t A)]
  -- Step 2: Unfold `correlationInfinite` on both sides and use the
  -- per-stage shift identity.
  unfold correlationInfinite
  congr 1
  funext n
  exact correlationAlongExhaustion_shift_vaddFinset_eq G Λ t p A n

/-! ## Translation invariance of truncated correlations -/

/-- **Translation of a singleton**: `vaddFinset t {i} = {t +ᵥ i}`. -/
@[simp]
theorem vaddFinset_singleton {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V] (t : T) (i : V) :
    vaddFinset t ({i} : Finset V) = {t +ᵥ i} := by
  unfold vaddFinset; rw [Finset.image_singleton]

/-- **Translation of a pair**: `vaddFinset t {i, j} = {t +ᵥ i, t +ᵥ j}`. -/
@[simp]
theorem vaddFinset_pair {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V] (t : T) (i j : V) :
    vaddFinset t ({i, j} : Finset V) = {t +ᵥ i, t +ᵥ j} := by
  unfold vaddFinset
  rw [Finset.image_insert, Finset.image_singleton]

/-- **Translation of a triple**:
`vaddFinset t {i, j, k} = {t +ᵥ i, t +ᵥ j, t +ᵥ k}`. -/
@[simp]
theorem vaddFinset_triple {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V] (t : T) (i j k : V) :
    vaddFinset t ({i, j, k} : Finset V) = {t +ᵥ i, t +ᵥ j, t +ᵥ k} := by
  unfold vaddFinset
  rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton]

/-- **Translation of a quadruple**:
`vaddFinset t {i, j, k, l} = {t +ᵥ i, t +ᵥ j, t +ᵥ k, t +ᵥ l}`. -/
@[simp]
theorem vaddFinset_quadruple {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V] (t : T) (i j k l : V) :
    vaddFinset t ({i, j, k, l} : Finset V)
      = {t +ᵥ i, t +ᵥ j, t +ᵥ k, t +ᵥ l} := by
  unfold vaddFinset
  rw [Finset.image_insert, Finset.image_insert,
      Finset.image_insert, Finset.image_singleton]

set_option linter.unusedFintypeInType false in
/-- **Translation invariance of the truncated 2-point correlation at
infinite volume**: for `IsTranslationInvariant T G` and ferromagnetic `p`,

`truncated2Infinite G Λ p (t +ᵥ i) (t +ᵥ j) = truncated2Infinite G Λ p i j`.

Direct consequence of the three ∞-volume correlation equalities
(`correlationInfinite_vaddFinset_of_translationInvariant` applied at
the singletons `{i}`, `{j}`, and the pair `{i, j}`). -/
theorem truncated2Infinite_translation
    {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (Λ : Exhaustion V) (t : T)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : V) :
    truncated2Infinite G Λ p (t +ᵥ i) (t +ᵥ j)
      = truncated2Infinite G Λ p i j := by
  unfold truncated2Infinite
  rw [show ({t +ᵥ i, t +ᵥ j} : Finset V) = vaddFinset t {i, j} from
        (vaddFinset_pair t i j).symm,
      show ({t +ᵥ i} : Finset V) = vaddFinset t {i} from
        (vaddFinset_singleton t i).symm,
      show ({t +ᵥ j} : Finset V) = vaddFinset t {j} from
        (vaddFinset_singleton t j).symm,
      correlationInfinite_vaddFinset_of_translationInvariant G Λ t p hf {i, j},
      correlationInfinite_vaddFinset_of_translationInvariant G Λ t p hf {i},
      correlationInfinite_vaddFinset_of_translationInvariant G Λ t p hf {j}]

set_option linter.unusedFintypeInType false in
/-- **Translation invariance of the truncated 3-point correlation at
infinite volume**: specialisation of
`correlationInfinite_vaddFinset_of_translationInvariant` at the seven
Ursell-expansion terms. -/
theorem truncated3Infinite_translation
    {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (Λ : Exhaustion V) (t : T)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : V) :
    truncated3Infinite G Λ p (t +ᵥ i) (t +ᵥ j) (t +ᵥ k)
      = truncated3Infinite G Λ p i j k := by
  unfold truncated3Infinite
  rw [show ({t +ᵥ i, t +ᵥ j, t +ᵥ k} : Finset V) = vaddFinset t {i, j, k} from
        (vaddFinset_triple t i j k).symm,
      show ({t +ᵥ j, t +ᵥ k} : Finset V) = vaddFinset t {j, k} from
        (vaddFinset_pair t j k).symm,
      show ({t +ᵥ i, t +ᵥ k} : Finset V) = vaddFinset t {i, k} from
        (vaddFinset_pair t i k).symm,
      show ({t +ᵥ i, t +ᵥ j} : Finset V) = vaddFinset t {i, j} from
        (vaddFinset_pair t i j).symm,
      show ({t +ᵥ i} : Finset V) = vaddFinset t {i} from
        (vaddFinset_singleton t i).symm,
      show ({t +ᵥ j} : Finset V) = vaddFinset t {j} from
        (vaddFinset_singleton t j).symm,
      show ({t +ᵥ k} : Finset V) = vaddFinset t {k} from
        (vaddFinset_singleton t k).symm,
      correlationInfinite_vaddFinset_of_translationInvariant G Λ t p hf {i, j, k},
      correlationInfinite_vaddFinset_of_translationInvariant G Λ t p hf {j, k},
      correlationInfinite_vaddFinset_of_translationInvariant G Λ t p hf {i, k},
      correlationInfinite_vaddFinset_of_translationInvariant G Λ t p hf {i, j},
      correlationInfinite_vaddFinset_of_translationInvariant G Λ t p hf {i},
      correlationInfinite_vaddFinset_of_translationInvariant G Λ t p hf {j},
      correlationInfinite_vaddFinset_of_translationInvariant G Λ t p hf {k}]

set_option linter.unusedFintypeInType false in
/-- **Translation invariance of the Lebowitz 4-point correlation at
infinite volume**. -/
theorem truncated4Infinite_translation
    {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (Λ : Exhaustion V) (t : T)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k l : V) :
    truncated4Infinite G Λ p (t +ᵥ i) (t +ᵥ j) (t +ᵥ k) (t +ᵥ l)
      = truncated4Infinite G Λ p i j k l := by
  unfold truncated4Infinite
  rw [show ({t +ᵥ i, t +ᵥ j, t +ᵥ k, t +ᵥ l} : Finset V)
        = vaddFinset t {i, j, k, l} from (vaddFinset_quadruple t i j k l).symm,
      show ({t +ᵥ i, t +ᵥ j} : Finset V) = vaddFinset t {i, j} from
        (vaddFinset_pair t i j).symm,
      show ({t +ᵥ k, t +ᵥ l} : Finset V) = vaddFinset t {k, l} from
        (vaddFinset_pair t k l).symm,
      show ({t +ᵥ i, t +ᵥ k} : Finset V) = vaddFinset t {i, k} from
        (vaddFinset_pair t i k).symm,
      show ({t +ᵥ j, t +ᵥ l} : Finset V) = vaddFinset t {j, l} from
        (vaddFinset_pair t j l).symm,
      show ({t +ᵥ i, t +ᵥ l} : Finset V) = vaddFinset t {i, l} from
        (vaddFinset_pair t i l).symm,
      show ({t +ᵥ j, t +ᵥ k} : Finset V) = vaddFinset t {j, k} from
        (vaddFinset_pair t j k).symm,
      correlationInfinite_vaddFinset_of_translationInvariant G Λ t p hf {i, j, k, l},
      correlationInfinite_vaddFinset_of_translationInvariant G Λ t p hf {i, j},
      correlationInfinite_vaddFinset_of_translationInvariant G Λ t p hf {k, l},
      correlationInfinite_vaddFinset_of_translationInvariant G Λ t p hf {i, k},
      correlationInfinite_vaddFinset_of_translationInvariant G Λ t p hf {j, l},
      correlationInfinite_vaddFinset_of_translationInvariant G Λ t p hf {i, l},
      correlationInfinite_vaddFinset_of_translationInvariant G Λ t p hf {j, k}]

/-! ## Translation invariance of free energy -/

/-- **Translation invariance of `freeEnergyΛ`**: for a
translation-invariant graph `G`,
`freeEnergyΛ G (vaddFinset t Λ) p = freeEnergyΛ G Λ p`.

Via `partitionFunctionΛ_vaddFinset_eq` (numerator) and
`Fintype.card_coe ∘ vaddFinset_card` (denominator). -/
theorem freeEnergyΛ_vaddFinset_eq {T : Type u} [AddGroup T]
    {V : Type v} [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (t : T) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    [Fintype (inducedGraph G (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) :
    freeEnergyΛ G (vaddFinset t Λ) p = freeEnergyΛ G Λ p := by
  change IsingModel.freeEnergy (inducedGraph G (vaddFinset t Λ)) p
    = IsingModel.freeEnergy (inducedGraph G Λ) p
  unfold IsingModel.freeEnergy
  have hZ : IsingModel.partitionFunction (inducedGraph G (vaddFinset t Λ)) p
      = IsingModel.partitionFunction (inducedGraph G Λ) p := by
    change partitionFunctionΛ G (vaddFinset t Λ) p = partitionFunctionΛ G Λ p
    exact partitionFunctionΛ_vaddFinset_eq G t Λ p
  have hcard : (Fintype.card (↑(vaddFinset t Λ) : Type _) : ℝ)
      = (Fintype.card (↑Λ : Type _) : ℝ) := by
    simp [Fintype.card_coe, vaddFinset_card]
  rw [hZ, hcard]

set_option linter.unusedFintypeInType false in
/-- **Translation invariance of `freeEnergyAlongExhaustion` under shift**:
for translation-invariant `G`,
`freeEnergyAlongExhaustion G (Λ.shift t) p n = freeEnergyAlongExhaustion G Λ p n`. -/
theorem freeEnergyAlongExhaustion_shift_eq
    {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (Λ : Exhaustion V) (t : T)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [hF2 : ∀ n, Fintype (inducedGraph G ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G (Λ.shift t) p n
      = freeEnergyAlongExhaustion G Λ p n := by
  -- Use explicit @ application to pin the Fintype instance on the
  -- `vaddFinset t (Λ.volume n)` shape, then rely on definitional
  -- equality with `(Λ.shift t).volume n`.
  exact @freeEnergyΛ_vaddFinset_eq _ _ _ _ _ G _ t (Λ.volume n) _ (hF2 n) p

set_option linter.unusedFintypeInType false in
/-- **Shift invariance of `freeEnergyInfinite`** (limsup side):
for a translation-invariant `G`,
`freeEnergyInfinite G (Λ.shift t) p = freeEnergyInfinite G Λ p`.

Direct consequence: the two `freeEnergyAlongExhaustion` sequences agree
pointwise (`freeEnergyAlongExhaustion_shift_eq`), hence their `limsup`
at `atTop` coincide. -/
theorem freeEnergyInfinite_shift_eq
    {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (Λ : Exhaustion V) (t : T)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) :
    freeEnergyInfinite G (Λ.shift t) p = freeEnergyInfinite G Λ p := by
  unfold freeEnergyInfinite
  congr 1
  funext n
  exact freeEnergyAlongExhaustion_shift_eq G Λ t p n

/-! ## Translation invariance of spontaneous quantities -/

set_option linter.unusedFintypeInType false in
/-- **Translation invariance of `spontaneousCorrelation`**: for a
translation-invariant graph `G` with ferromagnetic parameters `J ≥ 0`,
`β > 0`, and any translation `t : T`,

`spontaneousCorrelation G Λ J β (vaddFinset t A)
  = spontaneousCorrelation G Λ J β A`.

Proof: the infimum is over `h : Ioi 0`; at each `h`, the parameter
`⟨J, h, β⟩` is ferromagnetic (since `h > 0`, `0 ≤ J`, `0 < β`), so
`correlationInfinite_vaddFinset_of_translationInvariant` applies
pointwise. Hence the families over `h` agree pointwise and the infima
coincide. -/
theorem spontaneousCorrelation_translation
    {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (Λ : Exhaustion V) (t : T)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G ((Λ.shift t).volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    spontaneousCorrelation G Λ J β (vaddFinset t A)
      = spontaneousCorrelation G Λ J β A := by
  unfold spontaneousCorrelation
  congr 1
  funext h
  -- Apply `correlationInfinite_vaddFinset_of_translationInvariant` at `⟨J, h, β⟩`;
  -- the Ferromagnetic hypothesis is supplied by `h > 0`, `0 ≤ J`, `0 < β`.
  have hf : Ferromagnetic ⟨J, h.val, β⟩ :=
    ⟨hJ, le_of_lt h.property, hβ⟩
  exact correlationInfinite_vaddFinset_of_translationInvariant
    G Λ t ⟨J, h.val, β⟩ hf A

set_option linter.unusedFintypeInType false in
/-- **Translation invariance of `spontaneousMagnetization`**:
single-site specialisation of `spontaneousCorrelation_translation`
at `A = {i}`. -/
theorem spontaneousMagnetization_translation
    {T : Type u} [AddGroup T] {V : Type v}
    [DecidableEq V] [AddAction T V]
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    (Λ : Exhaustion V) (t : T)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G ((Λ.shift t).volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    spontaneousMagnetization G Λ J β (t +ᵥ i)
      = spontaneousMagnetization G Λ J β i := by
  -- `spontaneousMagnetization G Λ J β i = spontaneousCorrelation G Λ J β {i}`.
  rw [← spontaneousCorrelation_singleton_eq_spontaneousMagnetization G Λ J β (t +ᵥ i),
      ← spontaneousCorrelation_singleton_eq_spontaneousMagnetization G Λ J β i,
      show ({t +ᵥ i} : Finset V) = vaddFinset t {i} from
        (vaddFinset_singleton t i).symm,
      spontaneousCorrelation_translation G Λ t hJ hβ {i}]

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
p. 68. -/
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
  /-- `shift` is an additive monoid homomorphism `ℕ → T`:
  `shift (m + n) = shift m + shift n`. This is the structural datum
  that makes the tower "regular" and allows
  `volume (m + n) = volume m ∪ (shift m +ᵥ volume n)`. -/
  shift_add : ∀ m n, shift (m + n) = shift m + shift n

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

/-- **Decomposition of `volume (m + n)` as a union**: under the
additive `shift_add` structural field,
`volume (m + n) = volume m ∪ (shift m +ᵥ volume n)`.

Proof by induction on `n`. The base case uses `volume_zero`,
`vaddFinset_empty`, and `Finset.union_empty`; the inductive step
uses `volume_succ` (twice), `vaddFinset_union`, `vaddFinset_add`,
`shift_add`, and `Finset.union_assoc`. -/
theorem volume_decomposes
    (Λ : TranslationInvariantExhaustion T V) (m n : ℕ) :
    Λ.volume (m + n)
      = Λ.volume m ∪ vaddFinset (Λ.shift m) (Λ.volume n) := by
  induction n with
  | zero =>
    rw [Nat.add_zero, Λ.volume_zero, vaddFinset_empty,
        Finset.union_empty]
  | succ n ih =>
    -- LHS: Λ.volume (m + (n + 1)) = Λ.volume (m + n + 1)
    --    = Λ.volume (m + n) ∪ (shift (m+n) +ᵥ Λ.volume 1) [volume_succ]
    -- RHS: Λ.volume m ∪ (shift m +ᵥ Λ.volume (n + 1))
    --    = Λ.volume m ∪ (shift m +ᵥ (Λ.volume n ∪ (shift n +ᵥ Λ.volume 1)))
    --    = Λ.volume m ∪ ((shift m +ᵥ Λ.volume n) ∪
    --                    (shift m +ᵥ (shift n +ᵥ Λ.volume 1)))
    --    = Λ.volume m ∪ ((shift m +ᵥ Λ.volume n) ∪
    --                    ((shift m + shift n) +ᵥ Λ.volume 1))
    --    = Λ.volume m ∪ ((shift m +ᵥ Λ.volume n) ∪
    --                    (shift (m+n) +ᵥ Λ.volume 1)) [shift_add]
    --    = (Λ.volume m ∪ (shift m +ᵥ Λ.volume n)) ∪
    --      (shift (m+n) +ᵥ Λ.volume 1) [union_assoc]
    --    = Λ.volume (m+n) ∪ (shift (m+n) +ᵥ Λ.volume 1) [IH]
    --    = LHS.
    have hstep : m + (n + 1) = (m + n) + 1 := by ring
    rw [hstep, Λ.volume_succ (m + n), Λ.volume_succ n, ih,
        vaddFinset_union, vaddFinset_add, Λ.shift_add m n,
        Finset.union_assoc]

/-- **Disjointness of `volume m` and `shift m +ᵥ volume n`**:
under the `TranslationInvariantExhaustion` structure,
`Disjoint (volume m) (vaddFinset (shift m) (volume n))`.

Proof by induction on `n`. Base case `n = 0` reduces to `Disjoint _ ∅`
(trivial via `Finset.disjoint_empty_right`). Inductive step uses
the decomposition `vaddFinset (shift m) (volume (n+1)) = (shift m +ᵥ
volume n) ∪ (shift(m+n) +ᵥ volume 1)` (via `volume_succ`,
`vaddFinset_union`, `vaddFinset_add`, `shift_add`), the IH, and
`disjoint_shift (m+n)` combined with
`Λ.volume m ⊆ Λ.volume (m+n)` (from `Λ.mono`) to transfer disjointness. -/
theorem disjoint_volume_shift
    (Λ : TranslationInvariantExhaustion T V) (m n : ℕ) :
    Disjoint (Λ.volume m) (vaddFinset (Λ.shift m) (Λ.volume n)) := by
  induction n with
  | zero =>
    rw [Λ.volume_zero, vaddFinset_empty]
    exact Finset.disjoint_empty_right _
  | succ n ih =>
    -- vaddFinset (shift m) (volume (n+1))
    --   = vaddFinset (shift m) (volume n ∪ (shift n +ᵥ volume 1))
    --   = (shift m +ᵥ volume n) ∪ (shift m +ᵥ (shift n +ᵥ volume 1))
    --   = (shift m +ᵥ volume n) ∪ ((shift m + shift n) +ᵥ volume 1)
    --   = (shift m +ᵥ volume n) ∪ (shift (m+n) +ᵥ volume 1)
    rw [Λ.volume_succ n, vaddFinset_union, vaddFinset_add,
        ← Λ.shift_add m n]
    -- Show Disjoint Λ_m ((shift m +ᵥ Λ_n) ∪ (shift(m+n) +ᵥ Λ_1)).
    rw [Finset.disjoint_union_right]
    refine ⟨ih, ?_⟩
    -- Disjoint Λ_m (shift(m+n) +ᵥ Λ_1):
    -- since Λ_m ⊆ Λ_{m+n} (by mono), and disjoint_shift gives
    -- Disjoint Λ_{m+n} (shift(m+n) +ᵥ Λ_1).
    exact (Λ.disjoint_shift (m + n)).mono_left (Λ.mono (Nat.le_add_right m n))

set_option linter.unusedFintypeInType false in
/-- **`hsuper` in union form from translation invariance**: for a
translation-invariant graph `G`, a translation-invariant exhaustion
`Λ` with additive shift, and ferromagnetic parameters,

`log Z_{Λ.volume m} + log Z_{Λ.volume n}
  ≤ log Z_{Λ.volume m ∪ vaddFinset (Λ.shift m) (Λ.volume n)}`.

The RHS is, by `volume_decomposes` (step 7),
`log Z_{Λ.volume (m + n)}` — so this is the same statement as the
target `hsuper` field of `DisjointTowerHypotheses`, modulo the
Finset rewrite. Stating it in the union form avoids Fintype-instance
juggling that arises when applying `volume_decomposes` as a rewrite
through the partitionFunction indexed by a Fintype typeclass.

Proof: combine
1. `partitionFunctionΛ_vaddFinset_eq` (PR #237) — translation
   invariance of Z, reduces `log Z_{shift m +ᵥ Λ_n}` to
   `log Z_{Λ_n}`.
2. `log_partitionFunctionΛ_disjUnion_super_additive` — super-
   additivity on disjoint union (ferromagnetic).
3. `disjoint_volume_shift` (step 8) — supplies the disjointness. -/
theorem log_partitionFunctionΛ_super_of_translationInvariant_union
    (Λ : TranslationInvariantExhaustion T V)
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (m n : ℕ)
    [Fintype (inducedGraph G
        (vaddFinset (Λ.shift m) (Λ.volume n))).edgeSet]
    [Fintype (inducedGraph G
        (Λ.volume m ∪ vaddFinset (Λ.shift m) (Λ.volume n))).edgeSet] :
    Real.log (partitionFunctionΛ G (Λ.volume m) p)
      + Real.log (partitionFunctionΛ G (Λ.volume n) p)
      ≤ Real.log (partitionFunctionΛ G
          (Λ.volume m ∪ vaddFinset (Λ.shift m) (Λ.volume n)) p) := by
  have h_translate :
      partitionFunctionΛ G (vaddFinset (Λ.shift m) (Λ.volume n)) p
        = partitionFunctionΛ G (Λ.volume n) p :=
    partitionFunctionΛ_vaddFinset_eq G (Λ.shift m) (Λ.volume n) p
  have h_super := log_partitionFunctionΛ_disjUnion_super_additive
    (G := G) (hd := Λ.disjoint_volume_shift m n) p hf
  rw [h_translate] at h_super
  exact h_super

set_option linter.unusedFintypeInType false in
/-- **`hsuper` in `volume (m + n)` form**: bridges step 9's union
form to the form expected by `DisjointTowerHypotheses.super`.

Proof: apply step 9 (union form), then `partitionFunctionΛ_congr_finset`
with `volume_decomposes` to rewrite the RHS Finset. -/
theorem log_partitionFunctionΛ_super_of_translationInvariant
    (Λ : TranslationInvariantExhaustion T V)
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (m n : ℕ)
    [Fintype (inducedGraph G
        (vaddFinset (Λ.shift m) (Λ.volume n))).edgeSet]
    [Fintype (inducedGraph G
        (Λ.volume m ∪ vaddFinset (Λ.shift m) (Λ.volume n))).edgeSet] :
    Real.log (partitionFunctionΛ G (Λ.volume m) p)
      + Real.log (partitionFunctionΛ G (Λ.volume n) p)
      ≤ Real.log (partitionFunctionΛ G (Λ.volume (m + n)) p) := by
  have h_union := log_partitionFunctionΛ_super_of_translationInvariant_union
    Λ G p hf m n
  have h_eq := partitionFunctionΛ_congr_finset (G := G)
    (Λ.volume_decomposes m n).symm (p := p)
  rw [← h_eq]
  exact h_union

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
p. 68. -/
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
p. 68. -/
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

set_option linter.unusedFintypeInType false in
/-- **Automatic Fekete convergence under full translation
invariance** (GJ §4.6 Prop 4.6.1, p. 68): final step of the
translation scaffolding. Given

* a translation-invariant exhaustion `Λ` (step 3 / PR #222 +
  step 7 / PR #238);
* a translation-invariant graph `G` (step 1 / PR #220);
* ferromagnetic parameters `p` (for the disjoint-union
  super-additivity);
* bounded edge density along `Λ` (discharges `hbdd` via
  PR #203 / `BddAbove_freeEnergyAlongExhaustion_range`);
* auxiliary Fintype instances for the translated and union
  Finsets (required for the `log Z` super-additivity statement);
* `hcard_one`: non-degenerate base block,

the exhaustion free-energy density tends to the infinite-volume
free energy:
`freeEnergyAlongExhaustion G Λ.toExhaustion p` converges to
`freeEnergyInfinite G Λ.toExhaustion p`.

The `hsuper` input of previous steps is now discharged automatically
via `log_partitionFunctionΛ_super_of_translationInvariant`. -/
theorem freeEnergyAlongExhaustion_tendsto_of_translationInvariant_auto
    (Λ : TranslationInvariantExhaustion T V)
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ m n, Fintype (inducedGraph G
        (vaddFinset (Λ.shift m) (Λ.volume n))).edgeSet]
    [∀ m n, Fintype (inducedGraph G
        (Λ.volume m ∪ vaddFinset (Λ.shift m) (Λ.volume n))).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (hBED : BoundedEdgeDensity G Λ.toExhaustion)
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto (freeEnergyAlongExhaustion G Λ.toExhaustion p)
      Filter.atTop
      (nhds (freeEnergyInfinite G Λ.toExhaustion p)) :=
  freeEnergyAlongExhaustion_tendsto_of_translationInvariant Λ G p hBED
    (fun m n =>
      log_partitionFunctionΛ_super_of_translationInvariant Λ G p hf m n)
    hcard_one

end TranslationInvariantExhaustion

end Ambient

end IsingModel
