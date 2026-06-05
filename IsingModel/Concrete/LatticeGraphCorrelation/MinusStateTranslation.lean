import IsingModel.Concrete.LatticeGraphCorrelation.PlusStateTranslationGeneralHeadline

/-!
# Translation invariance of the `−`-state functional on ℤ^d (Issue #3581)

The `−`-state translation invariance follows from the `+`-state one
(`plusStateExpectation_vadd`) through the spin-flip bridge: `minusStateExpectation
J h β O = plusStateExpectation J (−h) β O.flipObs`, and translation commutes with the
flip (`configVaddEquiv` commutes with `Config.flip`).

* `flipObs_vadd_phi_eq` — the flip of a translate equals the translate of the flip.
* `minusStateExpectation_vadd` — translation invariance for the `−` state.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.4 Theorem 3.17 (statement p. 95, proof pp. 102–103).
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **The flip commutes with the translation pullback**: flipping then pulling back
through `configVaddEquiv` agrees with pulling back then flipping (both act
coordinatewise). -/
theorem flipObs_vadd_phi_eq {d : ℕ} (a : Fin d → ℤ) (O : LocalObservable d)
    (σ : Config (↑(LocalObservable.vadd a O).S : Type _)) :
    (LocalObservable.vadd a O).flipObs.φ σ = (O.flipObs.vadd a).φ σ := rfl

/-- **Translation invariance of the cubic-exhaustion `−`-state functional** (FV
Theorem 3.17): `μ⁻(τ_a φ) = μ⁻(φ)`.  Follows from the `+`-state invariance via the
spin-flip bridge. -/
theorem minusStateExpectation_vadd {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (a : Fin d → ℤ) (O : LocalObservable d) (hS : O.S ⊆ cubicBox d N)
    (hSvadd : (LocalObservable.vadd a O).S ⊆ cubicBox d (N + latticeRadius a)) :
    minusStateExpectation J h β (LocalObservable.vadd a O) hSvadd
      = minusStateExpectation J h β O hS := by
  have key : plusStateExpectation J (-h) β
        (⟨(LocalObservable.vadd a O).flipObs.S, (LocalObservable.vadd a O).flipObs.φ⟩
          : LocalObservable d) hSvadd
      = plusStateExpectation J (-h) β (⟨O.flipObs.S, O.flipObs.φ⟩ : LocalObservable d) hS := by
    rw [← plusStateExpectation_vadd (h := -h) hβ hJ a O.flipObs hS]
    exact plusStateExpectation_congr_phi (funext (fun σ => flipObs_vadd_phi_eq a O σ)) hSvadd
  exact key

end Ambient

end IsingModel
