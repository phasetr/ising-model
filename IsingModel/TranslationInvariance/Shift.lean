import IsingModel.TranslationInvariance.Finset

universe u v

namespace IsingModel

namespace Ambient

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

end Ambient

end IsingModel
