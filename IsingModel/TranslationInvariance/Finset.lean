import IsingModel.TranslationInvariance.Core

universe u v

namespace IsingModel

namespace Ambient

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


end Ambient

end IsingModel
