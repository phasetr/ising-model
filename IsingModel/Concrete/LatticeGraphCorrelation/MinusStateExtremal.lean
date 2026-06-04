import IsingModel.Concrete.LatticeGraphCorrelation.LocalObservableState
import IsingModel.Inequalities.BoundaryFlip

/-!
# The `−`-state functional and the `±` extremal ordering on ℤ^d (FV Theorem 3.17)

Obtains the `−` boundary state of a local observable from the `+`-state functional
(`LocalObservableState.lean`) via the global spin-flip symmetry `σ ↦ σ.flip` with
the field reflected `h ↦ −h` (`gibbsExpectationBC_minus_eq_plus_neg_h_flip`), and
proves the `±` extremal ordering `μ⁻(φ) ≤ μ⁺(φ)` for monotone observables.

* `LocalObservable.flipObs` — the flipped observable `σ ↦ φ(σ.flip)`.
* `minusStateExpectation` — the cubic-exhaustion `−`-state functional, defined as
  the `+`-state functional of the flipped observable at field `−h`.
* `tendsto_minusStateExpectation` and the transferred linearity / normalisation /
  positivity (`minusStateExpectation_{add,const_mul,const,nonneg}`).
* `plusBoxObsExpectation_flipObs_neg_h_le` — the finite-volume `−` ≤ `+` ordering
  (the flip bridge plus `gibbsExpectationBC_minus_le`).
* `minusStateExpectation_le_plusStateExpectation` — the infinite-volume `±`
  extremal ordering for monotone observables.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
§3.4 Theorem 3.17 (the extremal `±` states).
-/

namespace IsingModel

namespace Ambient

open Finset Filter Topology

/-- **The flipped observable**: `φ` precomposed with the global spin flip,
`σ ↦ φ(σ.flip)`, on the same support. -/
def LocalObservable.flipObs {d : ℕ} (O : LocalObservable d) : LocalObservable d :=
  ⟨O.S, fun σ => O.φ (Config.flip σ)⟩

/-- **The cubic-exhaustion `−`-state functional**: the `+`-state functional of the
flipped observable at the reflected field `−h` (the global spin-flip symmetry maps
the `−` boundary state to the `+` boundary state with `h ↦ −h`). -/
noncomputable def minusStateExpectation {d N : ℕ} (J h β : ℝ) (O : LocalObservable d)
    (hS : O.S ⊆ cubicBox d N) : ℝ :=
  plusStateExpectation J (-h) β O.flipObs hS

/-- **The screened `−` box expectations converge to the `−`-state functional**. -/
theorem tendsto_minusStateExpectation {d N : ℕ} {J h β : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (O : LocalObservable d) (hS : O.S ⊆ cubicBox d N) :
    Tendsto (fun k => plusBoxObsExpectation (N + k) (N + k + 1) J (-h) β O.flipObs
        (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1)))) atTop
      (nhds (minusStateExpectation J h β O hS)) :=
  tendsto_plusStateExpectation (h := -h) hβ hJ O.flipObs hS

/-- **Additivity of the `−`-state functional** (same support). -/
theorem minusStateExpectation_add {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    {S : Finset (Fin d → ℤ)} (φ₁ φ₂ : Config (↑S : Type _) → ℝ) (hS : S ⊆ cubicBox d N) :
    minusStateExpectation J h β (⟨S, fun σ => φ₁ σ + φ₂ σ⟩ : LocalObservable d) hS
      = minusStateExpectation J h β (⟨S, φ₁⟩ : LocalObservable d) hS
        + minusStateExpectation J h β (⟨S, φ₂⟩ : LocalObservable d) hS :=
  plusStateExpectation_add (h := -h) hβ hJ (fun σ => φ₁ (Config.flip σ))
    (fun σ => φ₂ (Config.flip σ)) hS

/-- **Scalar homogeneity of the `−`-state functional** (same support). -/
theorem minusStateExpectation_const_mul {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    {S : Finset (Fin d → ℤ)} (c : ℝ) (φ : Config (↑S : Type _) → ℝ) (hS : S ⊆ cubicBox d N) :
    minusStateExpectation J h β (⟨S, fun σ => c * φ σ⟩ : LocalObservable d) hS
      = c * minusStateExpectation J h β (⟨S, φ⟩ : LocalObservable d) hS :=
  plusStateExpectation_const_mul (h := -h) hβ hJ c (fun σ => φ (Config.flip σ)) hS

/-- **Normalisation of the `−`-state functional**: the `−` expectation of a constant
is that constant. -/
theorem minusStateExpectation_const {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    {S : Finset (Fin d → ℤ)} (c : ℝ) (hS : S ⊆ cubicBox d N) :
    minusStateExpectation J h β (⟨S, fun _ => c⟩ : LocalObservable d) hS = c :=
  plusStateExpectation_const (h := -h) hβ hJ c hS

/-- **Positivity of the `−`-state functional**: the `−` expectation of a
nonnegative observable is nonnegative. -/
theorem minusStateExpectation_nonneg {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    {S : Finset (Fin d → ℤ)} {φ : Config (↑S : Type _) → ℝ} (hφ : ∀ σ, 0 ≤ φ σ)
    (hS : S ⊆ cubicBox d N) :
    0 ≤ minusStateExpectation J h β (⟨S, φ⟩ : LocalObservable d) hS :=
  plusStateExpectation_nonneg (h := -h) hβ hJ (fun σ => hφ (Config.flip σ)) hS

/-- **Finite-volume `−` ≤ `+` ordering**: for a monotone observable and `β, J ≥ 0`,
the `−` box expectation (realised as the flipped `+` expectation at `−h`) is at most
the `+` box expectation (the flip bridge `gibbsExpectationBC_minus_eq_plus_neg_h_flip`
plus boundary monotonicity `gibbsExpectationBC_minus_le`). -/
theorem plusBoxObsExpectation_flipObs_neg_h_le {d : ℕ} (n m : ℕ) {J h β : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (O : LocalObservable d) (hmono : Monotone O.φ)
    (hS : O.S ⊆ cubicBox d m) :
    plusBoxObsExpectation n m J (-h) β O.flipObs hS
      ≤ plusBoxObsExpectation n m J h β O hS := by
  unfold plusBoxObsExpectation plusBoxExpectation
  have hbridge := gibbsExpectationBC_minus_eq_plus_neg_h_flip
    (inducedGraph (latticeGraph d) (cubicBox d m)) β (fun _ => J) h (plusBoxInterior d n m)
    (fun τ => O.φ (restrictConfig hS τ))
  rw [show (fun σ : Config (↑(cubicBox d m) : Type _) => O.flipObs.φ (restrictConfig hS σ))
        = (fun σ => O.φ (restrictConfig hS (Config.flip σ))) from rfl, ← hbridge]
  exact gibbsExpectationBC_minus_le _ hβ (fun _ => hJ) _ (plusConfig _)
    (fun σ => O.φ (restrictConfig hS σ)) (hmono.comp (restrictConfig_monotone hS))

/-- **The `±` extremal ordering** (FV Theorem 3.17): for a monotone observable and
`β, J ≥ 0`, the infinite-volume `−`-state expectation is at most the `+`-state
expectation, `μ⁻(φ) ≤ μ⁺(φ)`.  Both are limits of the finite-volume box
expectations, ordered at each stage. -/
theorem minusStateExpectation_le_plusStateExpectation {d N : ℕ} {J h β : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (O : LocalObservable d) (hmono : Monotone O.φ)
    (hS : O.S ⊆ cubicBox d N) :
    minusStateExpectation J h β O hS ≤ plusStateExpectation J h β O hS :=
  le_of_tendsto_of_tendsto'
    (tendsto_minusStateExpectation hβ hJ O hS)
    (tendsto_plusStateExpectation (h := h) hβ hJ O hS)
    (fun _ => plusBoxObsExpectation_flipObs_neg_h_le _ _ hβ hJ O hmono _)

end Ambient

end IsingModel
