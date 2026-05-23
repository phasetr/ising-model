import IsingModel.TranslationInvariance.Truncated

universe u v

namespace IsingModel

namespace Ambient

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

end Ambient

end IsingModel
