import IsingModel.TranslationInvariance.InfiniteCorrelation

universe u v

namespace IsingModel

namespace Ambient

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

end Ambient

end IsingModel
