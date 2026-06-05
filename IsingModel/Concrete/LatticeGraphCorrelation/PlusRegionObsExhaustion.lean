import IsingModel.Concrete.LatticeGraphCorrelation.PlusRegionExhaustion
import IsingModel.Concrete.LatticeGraphCorrelation.MinusStateExtremal
import IsingModel.Concrete.LatticeGraphCorrelation.PlusStateTranslationGeneralHeadline

/-!
# Exhaustion independence for general observables and the `−` state (FV §3.4 Thm 3.17)

Extends the monotone-observable exhaustion independence
(`tendsto_plusRegionExpectation_exhaustion`) to **all** local observables, through the
monotone-difference decomposition `φ = upper − lower`, and transfers it to the `−`
state via the global spin-flip bridge (`minusStateExpectation = plusStateExpectation`
at `(−h, flipObs)`).  This completes FV Theorem 3.17 (`d ≥ 1`) for the cubic-exhaustion
`±`-state functionals on an arbitrary exhaustion.

* `plusRegionObsExpectation` — the region `+` expectation of a general observable.
* `plusRegionObsExpectation_eq_sub` — its upper/lower decomposition.
* `tendsto_plusRegionObsExpectation_exhaustion` — general-observable `+` convergence.
* `minusRegionObsExpectation` / `tendsto_minusRegionObsExpectation_exhaustion` — the
  `−`-state analogue.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.4 Theorem 3.17 (statement p. 95, proof pp. 102–103).
-/

namespace IsingModel

namespace Ambient

open Finset Filter Topology

variable {d : ℕ}

/-- **The region `+` expectation of a general local observable** `μ⁺_A(O)`: the
difference of the region `+` expectations of the upper and lower monotone parts
(the monotone-difference decomposition `φ = upper − lower`). -/
noncomputable def plusRegionObsExpectation (A : Finset (Fin d → ℤ)) (J h β : ℝ)
    (O : LocalObservable d) (hSA : O.S ⊆ A) : ℝ :=
  plusRegionExpectation A J h β O.upper hSA - plusRegionExpectation A J h β O.lower hSA

/-- **Upper/lower decomposition of the general region `+` expectation**: by
definition the region `+` expectation of `O` is the difference of those of its upper
and lower monotone parts. -/
theorem plusRegionObsExpectation_eq_sub (A : Finset (Fin d → ℤ)) (J h β : ℝ)
    (O : LocalObservable d) (hSA : O.S ⊆ A) :
    plusRegionObsExpectation A J h β O hSA
      = plusRegionExpectation A J h β O.upper hSA
        - plusRegionExpectation A J h β O.lower hSA :=
  rfl

/-- **Exhaustion independence of the `+`-state functional on a general observable**
(FV Theorem 3.17, `d ≥ 1`): for any exhaustion `Λ` of `ℤ^d` and any local observable
`O`, the region `+` expectations converge to the cubic-exhaustion `+`-state
`plusStateExpectation` — reducing to the monotone case through `φ = upper − lower`. -/
theorem tendsto_plusRegionObsExpectation_exhaustion (hd : 0 < d) {N : ℕ} {J h β : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (O : LocalObservable d) (hS : O.S ⊆ cubicBox d N)
    (Λ : Ambient.Exhaustion (Fin d → ℤ)) {N₀ : ℕ}
    (hN₀ : ∀ k, N₀ ≤ k → O.S ⊆ Λ.volume k) :
    Tendsto (fun k => plusRegionObsExpectation (Λ.volume (N₀ + k)) J h β O
        (hN₀ (N₀ + k) (Nat.le_add_right N₀ k))) atTop
      (nhds (plusStateExpectation J h β O hS)) := by
  rw [plusStateExpectation_eq_upper_sub_lower hβ hJ O hS]
  simp only [plusRegionObsExpectation]
  exact (tendsto_plusRegionExpectation_exhaustion hd hβ hJ O.upper hS Λ hN₀).sub
    (tendsto_plusRegionExpectation_exhaustion hd hβ hJ O.lower hS Λ hN₀)

/-- **The region `−` expectation of a general local observable** `μ⁻_A(O)`: the region
`+` expectation of the flipped observable at the reflected field `−h` (the global
spin-flip symmetry maps the `−` boundary state to the `+` state with `h ↦ −h`). -/
noncomputable def minusRegionObsExpectation (A : Finset (Fin d → ℤ)) (J h β : ℝ)
    (O : LocalObservable d) (hSA : O.S ⊆ A) : ℝ :=
  plusRegionObsExpectation A J (-h) β O.flipObs hSA

/-- **Exhaustion independence of the `−`-state functional** (FV Theorem 3.17, `d ≥ 1`):
for any exhaustion `Λ` of `ℤ^d` and any local observable `O`, the region `−`
expectations converge to the cubic-exhaustion `−`-state `minusStateExpectation` — the
`(−h, flipObs)` specialisation of the `+` headline. -/
theorem tendsto_minusRegionObsExpectation_exhaustion (hd : 0 < d) {N : ℕ} {J h β : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (O : LocalObservable d) (hS : O.S ⊆ cubicBox d N)
    (Λ : Ambient.Exhaustion (Fin d → ℤ)) {N₀ : ℕ}
    (hN₀ : ∀ k, N₀ ≤ k → O.S ⊆ Λ.volume k) :
    Tendsto (fun k => minusRegionObsExpectation (Λ.volume (N₀ + k)) J h β O
        (hN₀ (N₀ + k) (Nat.le_add_right N₀ k))) atTop
      (nhds (minusStateExpectation J h β O hS)) :=
  tendsto_plusRegionObsExpectation_exhaustion hd hβ hJ O.flipObs hS Λ hN₀

end Ambient

end IsingModel
