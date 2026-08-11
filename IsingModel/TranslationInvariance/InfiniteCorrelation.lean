import IsingModel.TranslationInvariance.FiniteVolume

/-!
# Translation invariance of the infinite-volume correlation of a translated observable

Both statements fix an additive group `T` acting on a vertex type `V` with `[DecidableEq V]`, a
graph `G : SimpleGraph V` carrying an `IsTranslationInvariant T G` instance, an exhaustion
`Λ : Exhaustion V`, a group element `t : T`, and stagewise `Fintype` instances on the edge sets of
the graphs induced by `G` on the volumes of `Λ` and on those of `Λ.shift t`, whose stage `n`
volume is the translate of the stage `n` volume of `Λ`.

The stagewise statement is an equality of `correlationAlongExhaustion` at each stage `n`, between
the shifted exhaustion at the translated observable `vaddFinset t A` and the original exhaustion
at `A`, for an arbitrary `p : IsingParams ℝ` and `A : Finset V`. Because
`correlationAlongExhaustion` is defined by a `dite` on whether the observable is contained in the
stage volume, the proof splits accordingly: translation preserves that containment in both
directions, so either both branches take the finite-volume correlation — matched by the lift
identity together with the finite-volume correlation identity — or both branches are `0`.

The infinite-volume statement adds `Ferromagnetic p`, that is `0 ≤ p.J`, `0 ≤ p.h` and `0 < p.β`,
and concludes `correlationInfinite G Λ p (vaddFinset t A) = correlationInfinite G Λ p A`. Since
`correlationInfinite` is the supremum over stages of `correlationAlongExhaustion`, the
ferromagnetic hypothesis is what allows the exhaustion to be replaced by `Λ.shift t` first; the
stagewise equality then matches the two families of stage values term by term.
-/

universe u v

namespace IsingModel

namespace Ambient

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

end Ambient

end IsingModel
