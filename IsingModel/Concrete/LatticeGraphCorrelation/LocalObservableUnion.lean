import IsingModel.Concrete.LatticeGraphCorrelation.MinusStateExtremal

/-!
# Cross-support union linearity of the `±`-state functional on ℤ^d

The same-support linearity of the cubic-exhaustion `±`-state functionals
(`plusStateExpectation_add`, `MinusStateExtremal.lean`) extends to observables on
*different* supports: an observable on `S₁` and one on `S₂` are both lifted to
`S₁ ∪ S₂` (where they ignore the extra coordinates), and the functional adds.

* `LocalObservable.extend` — enlarge the support of an observable (it ignores the
  new coordinates), with `plusBoxObsExpectation_extend_eq` (the box expectation is
  unchanged) and `plusStateExpectation_extend_eq` / `minusStateExpectation_extend_eq`
  (the `±`-state functional is unchanged).
* `plusStateExpectation_union_add` / `minusStateExpectation_union_add` — the
  cross-support additivity of the `±`-state functionals.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
§3.4 (local functions and the infinite-volume states).
-/

namespace IsingModel

namespace Ambient

open Finset Filter Topology

/-- **Support enlargement of a local observable**: `O` lifted to a larger support
`S'` by ignoring the extra coordinates (`φ` precomposed with the restriction back
to `O.S`). -/
def LocalObservable.extend {d : ℕ} (O : LocalObservable d) {S' : Finset (Fin d → ℤ)}
    (hSS' : O.S ⊆ S') : LocalObservable d :=
  ⟨S', fun σ => O.φ (restrictConfig hSS' σ)⟩

/-- **The `+` box expectation is unchanged under support enlargement**: the lifted
observable depends only on the inner configuration (`restrictConfig_trans`). -/
theorem plusBoxObsExpectation_extend_eq {d : ℕ} (n m : ℕ) (J h β : ℝ)
    (O : LocalObservable d) {S' : Finset (Fin d → ℤ)} (hSS' : O.S ⊆ S')
    (hS' : S' ⊆ cubicBox d m) :
    plusBoxObsExpectation n m J h β (O.extend hSS') hS'
      = plusBoxObsExpectation n m J h β O (hSS'.trans hS') := rfl

/-- **The `+`-state functional is unchanged under support enlargement**: both sides
are the limit of the same box-expectation sequence
(`plusBoxObsExpectation_extend_eq`). -/
theorem plusStateExpectation_extend_eq {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (O : LocalObservable d) {S' : Finset (Fin d → ℤ)} (hSS' : O.S ⊆ S')
    (hS' : S' ⊆ cubicBox d N) :
    plusStateExpectation J h β (O.extend hSS') hS'
      = plusStateExpectation J h β O (hSS'.trans hS') := by
  refine tendsto_nhds_unique (tendsto_plusStateExpectation (h := h) hβ hJ (O.extend hSS') hS') ?_
  have h2 := tendsto_plusStateExpectation (h := h) hβ hJ O (hSS'.trans hS')
  refine h2.congr (fun k => ?_)
  exact (plusBoxObsExpectation_extend_eq _ _ J h β O hSS' _).symm

/-- **The `−`-state functional is unchanged under support enlargement** (the flip
of an extension is the extension of the flip). -/
theorem minusStateExpectation_extend_eq {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (O : LocalObservable d) {S' : Finset (Fin d → ℤ)} (hSS' : O.S ⊆ S')
    (hS' : S' ⊆ cubicBox d N) :
    minusStateExpectation J h β (O.extend hSS') hS'
      = minusStateExpectation J h β O (hSS'.trans hS') :=
  plusStateExpectation_extend_eq (h := -h) hβ hJ O.flipObs hSS' hS'

/-- **Cross-support additivity of the `+`-state functional**: for observables on
`S₁` and `S₂`, both lifted to `S₁ ∪ S₂` (ignoring extra coordinates), the `+`
state of the sum is the sum of the `+` states. -/
theorem plusStateExpectation_union_add {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    {S₁ S₂ : Finset (Fin d → ℤ)} (φ₁ : Config (↑S₁ : Type _) → ℝ)
    (φ₂ : Config (↑S₂ : Type _) → ℝ) (hU : S₁ ∪ S₂ ⊆ cubicBox d N) :
    plusStateExpectation J h β
        (⟨S₁ ∪ S₂, fun σ => φ₁ (restrictConfig Finset.subset_union_left σ)
          + φ₂ (restrictConfig Finset.subset_union_right σ)⟩ : LocalObservable d) hU
      = plusStateExpectation J h β (⟨S₁, φ₁⟩ : LocalObservable d)
          (Finset.subset_union_left.trans hU)
        + plusStateExpectation J h β (⟨S₂, φ₂⟩ : LocalObservable d)
          (Finset.subset_union_right.trans hU) := by
  have e1 : plusStateExpectation J h β
        (⟨S₁ ∪ S₂, fun σ => φ₁ (restrictConfig Finset.subset_union_left σ)⟩ : LocalObservable d) hU
      = plusStateExpectation J h β (⟨S₁, φ₁⟩ : LocalObservable d)
          (Finset.subset_union_left.trans hU) :=
    plusStateExpectation_extend_eq (h := h) hβ hJ (⟨S₁, φ₁⟩ : LocalObservable d)
      Finset.subset_union_left hU
  have e2 : plusStateExpectation J h β
        (⟨S₁ ∪ S₂, fun σ => φ₂ (restrictConfig Finset.subset_union_right σ)⟩ : LocalObservable d) hU
      = plusStateExpectation J h β (⟨S₂, φ₂⟩ : LocalObservable d)
          (Finset.subset_union_right.trans hU) :=
    plusStateExpectation_extend_eq (h := h) hβ hJ (⟨S₂, φ₂⟩ : LocalObservable d)
      Finset.subset_union_right hU
  rw [plusStateExpectation_add (h := h) hβ hJ
      (fun σ => φ₁ (restrictConfig Finset.subset_union_left σ))
      (fun σ => φ₂ (restrictConfig Finset.subset_union_right σ)) hU, e1, e2]

/-- **Cross-support additivity of the `−`-state functional**. -/
theorem minusStateExpectation_union_add {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    {S₁ S₂ : Finset (Fin d → ℤ)} (φ₁ : Config (↑S₁ : Type _) → ℝ)
    (φ₂ : Config (↑S₂ : Type _) → ℝ) (hU : S₁ ∪ S₂ ⊆ cubicBox d N) :
    minusStateExpectation J h β
        (⟨S₁ ∪ S₂, fun σ => φ₁ (restrictConfig Finset.subset_union_left σ)
          + φ₂ (restrictConfig Finset.subset_union_right σ)⟩ : LocalObservable d) hU
      = minusStateExpectation J h β (⟨S₁, φ₁⟩ : LocalObservable d)
          (Finset.subset_union_left.trans hU)
        + minusStateExpectation J h β (⟨S₂, φ₂⟩ : LocalObservable d)
          (Finset.subset_union_right.trans hU) := by
  have e1 : minusStateExpectation J h β
        (⟨S₁ ∪ S₂, fun σ => φ₁ (restrictConfig Finset.subset_union_left σ)⟩ : LocalObservable d) hU
      = minusStateExpectation J h β (⟨S₁, φ₁⟩ : LocalObservable d)
          (Finset.subset_union_left.trans hU) :=
    minusStateExpectation_extend_eq (h := h) hβ hJ (⟨S₁, φ₁⟩ : LocalObservable d)
      Finset.subset_union_left hU
  have e2 : minusStateExpectation J h β
        (⟨S₁ ∪ S₂, fun σ => φ₂ (restrictConfig Finset.subset_union_right σ)⟩ : LocalObservable d) hU
      = minusStateExpectation J h β (⟨S₂, φ₂⟩ : LocalObservable d)
          (Finset.subset_union_right.trans hU) :=
    minusStateExpectation_extend_eq (h := h) hβ hJ (⟨S₂, φ₂⟩ : LocalObservable d)
      Finset.subset_union_right hU
  rw [minusStateExpectation_add (h := h) hβ hJ
      (fun σ => φ₁ (restrictConfig Finset.subset_union_left σ))
      (fun σ => φ₂ (restrictConfig Finset.subset_union_right σ)) hU, e1, e2]

end Ambient

end IsingModel
