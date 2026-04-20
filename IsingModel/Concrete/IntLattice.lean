import IsingModel.TranslationInvariance
import IsingModel.Lattice

/-!
# Translation-invariance instance for the `ℤ^d` nearest-neighbour graph

The graph `IsingModel.latticeGraph d : SimpleGraph (Fin d → ℤ)`
(defined in `IsingModel/Lattice.lean` via the ℓ¹-distance-1 adjacency)
is the standard `d`-dimensional lattice graph used throughout GJ §5.4.
This file records that it is translation invariant under the natural
additive action of `Fin d → ℤ` on itself, giving the first non-trivial
`Ambient.IsTranslationInvariant` instance beyond the trivial
`⊥`, `⊤` cases provided in `TranslationInvariance.lean`.

## Main result

* `isTranslationInvariant_latticeGraph`: for every `d : ℕ`, the
  lattice graph `IsingModel.latticeGraph d` is
  `Ambient.IsTranslationInvariant (Fin d → ℤ) (latticeGraph d)`
  under the standard pointwise additive action.

## Design note

The `TranslationInvariantExhaustion T V` structure additionally
requires a single-block tower `volume (n+1) = volume n ∪ (shift n +ᵥ
volume 1)` with `shift : ℕ → T` an additive homomorphism, combined
with `Exhaustion V.exhaust` covering every finite `A ⊆ V`. For
`V = Fin d → ℤ` these two requirements are not simultaneously
satisfiable by the natural cubic exhaustion
`Λ_n = {x : Fin d → ℤ | ∀ i, -n ≤ x i ≤ n}`, which adds more than
one block per step. Concrete construction of a
`TranslationInvariantExhaustion` for `ℤ^d` therefore requires a
structural refinement (e.g. block-pair shift, or a relaxation of
`Exhaustion`) and is deferred to a future PR. The present file
delivers only the translation-invariance datum.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.6 Prop 4.6.1, p. 68.
-/

namespace IsingModel

namespace Ambient

/-- **Translation invariance of the `ℤ^d` nearest-neighbour graph**:
for every `d : ℕ`, the standard lattice graph `latticeGraph d` on
`Fin d → ℤ` (edges between points at ℓ¹-distance 1) is preserved
by every translation `t +ᵥ ·` under the canonical self-action of
`Fin d → ℤ` on itself.

Formally, for every `t u v : Fin d → ℤ`,
`(latticeGraph d).Adj (t +ᵥ u) (t +ᵥ v) ↔ (latticeGraph d).Adj u v`,
which reduces to the pointwise identity `(t + u) i - (t + v) i = u i - v i`.

This is the first non-trivial `Ambient.IsTranslationInvariant`
instance (the prior ones are `⊥` and `⊤`). It is groundwork toward
GJ §4.6 Prop 4.6.1 (p. 68): the class is the structural datum
feeding into the automatic super-additivity of `log Z` along a
translation-invariant exhaustion; this file does not yet assemble a
concrete `TranslationInvariantExhaustion` (see the design note
above). -/
instance isTranslationInvariant_latticeGraph (d : ℕ) :
    Ambient.IsTranslationInvariant (Fin d → ℤ) (IsingModel.latticeGraph d) where
  adj_vadd := by
    intro t u v
    -- `vadd` on `Fin d → ℤ` is pointwise addition, so
    -- `(t +ᵥ u) i - (t +ᵥ v) i = u i - v i` for every coordinate `i`.
    change (∑ i : Fin d, |(t +ᵥ u) i - (t +ᵥ v) i|) = 1
      ↔ (∑ i : Fin d, |u i - v i|) = 1
    have hcoord : ∀ i : Fin d,
        |(t +ᵥ u) i - (t +ᵥ v) i| = |u i - v i| := by
      intro i
      have : (t +ᵥ u) i - (t +ᵥ v) i = u i - v i := by
        -- `vadd = (· + ·)` on self-action and pointwise on Pi
        simp [vadd_eq_add]
      rw [this]
    simp_rw [hcoord]

end Ambient

end IsingModel
