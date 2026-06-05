import IsingModel.Concrete.LatticeGraphCorrelation.PlusStateTranslationGeneral

/-!
# Translation invariance for all local observables (Issue #3581)

The final assembly: the cubic-exhaustion `+`-state functional is invariant under
lattice translations on **any** local observable, `μ⁺(τ_a φ) = μ⁺(φ)`, reducing the
general case to the monotone case (`plusStateExpectation_vadd_monotone`) through the
monotone-difference decomposition (the upper/lower parts commute with translation,
`vadd_upper_phi_eq` / `vadd_lower_phi_eq`).

* `plusStateExpectation_eq_upper_sub_lower` — the `+`-state as a difference of
  monotone `+`-states.
* `plusStateExpectation_vadd` — translation invariance for an arbitrary local
  observable.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.4 Theorem 3.17 (statement p. 95, proof pp. 102–103).
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **The monotone-difference decomposition of the `+`-state functional**: the
`+`-state of `O` is the `+`-state of its upper monotone part minus that of its lower
monotone part. -/
theorem plusStateExpectation_eq_upper_sub_lower {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β)
    (hJ : 0 ≤ J) (O : LocalObservable d) (hS : O.S ⊆ cubicBox d N) :
    plusStateExpectation J h β O hS
      = plusStateExpectation J h β (⟨O.upper.S, O.upper.φ⟩ : LocalObservable d) hS
        - plusStateExpectation J h β (⟨O.lower.S, O.lower.φ⟩ : LocalObservable d) hS := by
  rw [plusStateExpectation_of_monotone hβ hJ O.upper hS,
    plusStateExpectation_of_monotone hβ hJ O.lower hS]
  rfl

/-- **Translation invariance of the cubic-exhaustion `+`-state functional on any
local observable** (FV Theorem 3.17): `μ⁺(τ_a φ) = μ⁺(φ)`.  Reduces to the monotone
case through the monotone-difference decomposition, since translation commutes with
the upper/lower monotone parts. -/
theorem plusStateExpectation_vadd {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (a : Fin d → ℤ) (O : LocalObservable d) (hS : O.S ⊆ cubicBox d N)
    (hSvadd : (LocalObservable.vadd a O).S ⊆ cubicBox d (N + latticeRadius a)) :
    plusStateExpectation J h β (LocalObservable.vadd a O) hSvadd
      = plusStateExpectation J h β O hS := by
  have hup : plusStateExpectation J h β
        (⟨(LocalObservable.vadd a O).upper.S, (LocalObservable.vadd a O).upper.φ⟩
          : LocalObservable d) hSvadd
      = plusStateExpectation J h β (⟨O.upper.S, O.upper.φ⟩ : LocalObservable d) hS := by
    rw [← plusStateExpectation_vadd_monotone hβ hJ a O.upper hS]
    exact plusStateExpectation_congr_phi (funext (fun σ => vadd_upper_phi_eq a O σ)) hSvadd
  have hlo : plusStateExpectation J h β
        (⟨(LocalObservable.vadd a O).lower.S, (LocalObservable.vadd a O).lower.φ⟩
          : LocalObservable d) hSvadd
      = plusStateExpectation J h β (⟨O.lower.S, O.lower.φ⟩ : LocalObservable d) hS := by
    rw [← plusStateExpectation_vadd_monotone hβ hJ a O.lower hS]
    exact plusStateExpectation_congr_phi (funext (fun σ => vadd_lower_phi_eq a O σ)) hSvadd
  rw [plusStateExpectation_eq_upper_sub_lower hβ hJ (LocalObservable.vadd a O) hSvadd,
    plusStateExpectation_eq_upper_sub_lower hβ hJ O hS, hup, hlo]

end Ambient

end IsingModel
