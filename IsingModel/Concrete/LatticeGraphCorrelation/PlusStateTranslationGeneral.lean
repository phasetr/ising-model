import IsingModel.Concrete.LatticeGraphCorrelation.PlusStateTranslationHeadline

/-!
# Translation-invariance infrastructure for general local observables (Issue #3581)

The compatibility lemmas needed to extend the monotone-observable translation
invariance (`plusStateExpectation_vadd_monotone`) to **all** local observables via
the monotone-difference decomposition: the up-spin count and the monotone bound are
translation-invariant, so `LocalObservable.vadd`'s upper/lower parts agree with the
translates of `O`'s upper/lower parts.  The final assembly
(`plusStateExpectation_vadd`) is a short follow-up built on these.

* `configUpRank_configVaddEquiv_symm` — the up-spin count is translation-invariant.
* `LocalObservable.vadd` / `monoBound_vadd` — the translated observable and its
  translation-invariant monotone bound.
* `vadd_upper_phi_eq` / `vadd_lower_phi_eq` — the upper/lower parts commute with
  translation.
* `plusStateExpectation_congr_phi` — the `+`-state respects observable-function
  equality.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.4 Theorem 3.17 (statement p. 95, proof pp. 102–103).
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **The up-spin count is translation-invariant**: pulling a configuration on the
translated support back through `configVaddEquiv` preserves the number of `+` sites
(the pullback is a coordinate relabeling). -/
theorem configUpRank_configVaddEquiv_symm {d : ℕ} {S : Finset (Fin d → ℤ)} (a : Fin d → ℤ)
    (σ : Config (↑(vaddFinset a S) : Type _)) :
    configUpRank ((configVaddEquiv a S).symm σ) = configUpRank σ := by
  unfold configUpRank
  rw [← Finset.card_map (vaddSubtypeEquiv a S).toEmbedding]
  congr 1
  ext j
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rwa [configVaddEquiv_symm_apply] at hi
  · intro hj
    exact ⟨(vaddSubtypeEquiv a S).symm j, by rw [configVaddEquiv_symm_apply]; simpa using hj,
      by simp⟩

/-- **The lattice translation of a local observable** (no monotonicity required):
support translated by `a`, observable pulled back through `configVaddEquiv`. -/
noncomputable def LocalObservable.vadd {d : ℕ} (a : Fin d → ℤ) (O : LocalObservable d) :
    LocalObservable d :=
  ⟨vaddFinset a O.S, fun σ => O.φ ((configVaddEquiv a O.S).symm σ)⟩

/-- **The monotone bound is translation-invariant** (the pullback ranges over the
same observable values). -/
theorem monoBound_vadd {d : ℕ} (a : Fin d → ℤ) (O : LocalObservable d) :
    (LocalObservable.vadd a O).monoBound = O.monoBound := by
  simp only [LocalObservable.monoBound, LocalObservable.vadd]
  congr 1
  apply le_antisymm
  · apply Finset.sup'_le
    intro σ _
    exact Finset.le_sup' (fun τ => |O.φ τ|) (Finset.mem_univ _)
  · apply Finset.sup'_le
    intro τ _
    rw [show τ = (configVaddEquiv a O.S).symm (configVaddEquiv a O.S τ) by simp]
    exact Finset.le_sup' (fun σ => |O.φ ((configVaddEquiv a O.S).symm σ)|) (Finset.mem_univ _)

/-- **The upper part of the translate equals the translate of the upper part**: the
`+`-monotone part commutes with the translation (the up-spin count and the monotone
bound are translation-invariant). -/
theorem vadd_upper_phi_eq {d : ℕ} (a : Fin d → ℤ) (O : LocalObservable d)
    (σ : Config (↑(LocalObservable.vadd a O).S : Type _)) :
    (LocalObservable.vadd a O).upper.φ σ = (O.upper.vadd a).φ σ := by
  change (LocalObservable.vadd a O).monoBound * (configUpRank σ : ℝ)
      + (LocalObservable.vadd a O).φ σ
    = O.upper.φ ((configVaddEquiv a O.upper.S).symm σ)
  rw [monoBound_vadd]
  change O.monoBound * (configUpRank σ : ℝ) + O.φ ((configVaddEquiv a O.S).symm σ)
    = O.monoBound * (configUpRank ((configVaddEquiv a O.S).symm σ) : ℝ)
        + O.φ ((configVaddEquiv a O.S).symm σ)
  congr 1
  exact congrArg (fun r : ℕ => O.monoBound * (r : ℝ)) (configUpRank_configVaddEquiv_symm a σ).symm

/-- **The lower part of the translate equals the translate of the lower part**. -/
theorem vadd_lower_phi_eq {d : ℕ} (a : Fin d → ℤ) (O : LocalObservable d)
    (σ : Config (↑(LocalObservable.vadd a O).S : Type _)) :
    (LocalObservable.vadd a O).lower.φ σ = (O.lower.vadd a).φ σ := by
  change (LocalObservable.vadd a O).monoBound * (configUpRank σ : ℝ)
    = O.lower.φ ((configVaddEquiv a O.lower.S).symm σ)
  rw [monoBound_vadd]
  exact congrArg (fun r : ℕ => O.monoBound * (r : ℝ)) (configUpRank_configVaddEquiv_symm a σ).symm

/-- **The `+`-state functional respects observable equality** (same support, equal
function): equal observable functions have equal `+`-state. -/
theorem plusStateExpectation_congr_phi {d N : ℕ} {J h β : ℝ} {S : Finset (Fin d → ℤ)}
    {φ₁ φ₂ : Config (↑S : Type _) → ℝ} (hφ : φ₁ = φ₂) (hS : S ⊆ cubicBox d N) :
    plusStateExpectation J h β (⟨S, φ₁⟩ : LocalObservable d) hS
      = plusStateExpectation J h β (⟨S, φ₂⟩ : LocalObservable d) hS := by
  subst hφ; rfl

end Ambient

end IsingModel
