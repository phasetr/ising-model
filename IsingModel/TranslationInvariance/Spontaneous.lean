import IsingModel.TranslationInvariance.FreeEnergy

universe u v

namespace IsingModel

namespace Ambient

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

end Ambient

end IsingModel
