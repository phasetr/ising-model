import IsingModel.Concrete.LatticeGraphCorrelation.LocalObservableState
import IsingModel.Concrete.LatticeGraphCorrelation.MinusStateExtremal

/-!
# Box-independence of the cubic-exhaustion `+`-state functional (Issue #3599)

The `+`-state functional `plusStateExpectation J h β O hS` does not depend on the
witnessing box `N` of the support hypothesis `hS : O.S ⊆ cubicBox d N`: it is the limit
of the screened box expectations, and different witnesses give shifts of the same
sequence.

* `plusBoxObsExpectation_index_congr` — equal box radii give equal box expectations.
* `plusStateExpectation_congr_N` — box-independence of the `+`-state functional.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.4 Theorem 3.17.
-/

namespace IsingModel

namespace Ambient

open Finset Filter Topology

variable {d : ℕ}

/-- **Index congruence of the `+` box expectation**: equal box radii `(n,m) = (n',m')`
give equal box expectations (the support hypotheses are proof-irrelevant). -/
theorem plusBoxObsExpectation_index_congr {n n' m m' : ℕ} (hn : n = n') (hm : m = m')
    {J h β : ℝ} (O : LocalObservable d) (hS : O.S ⊆ cubicBox d m)
    (hS' : O.S ⊆ cubicBox d m') :
    plusBoxObsExpectation n m J h β O hS = plusBoxObsExpectation n' m' J h β O hS' := by
  subst hn; subst hm; rfl

/-- **Box-independence of the `+`-state functional**: `plusStateExpectation` does not
depend on the witnessing box `N` of the support hypothesis. -/
theorem plusStateExpectation_congr_N {N₁ N₂ : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (O : LocalObservable d) (hS₁ : O.S ⊆ cubicBox d N₁) (hS₂ : O.S ⊆ cubicBox d N₂) :
    plusStateExpectation J h β O hS₁ = plusStateExpectation J h β O hS₂ := by
  have key : ∀ {M₁ M₂ : ℕ} (g₁ : O.S ⊆ cubicBox d M₁) (g₂ : O.S ⊆ cubicBox d M₂),
      M₁ ≤ M₂ → plusStateExpectation J h β O g₁ = plusStateExpectation J h β O g₂ := by
    intro M₁ M₂ g₁ g₂ hM
    refine tendsto_nhds_unique ?_ (tendsto_plusStateExpectation hβ hJ O g₂)
    refine ((tendsto_plusStateExpectation hβ hJ O g₁).comp
      (tendsto_add_atTop_nat (M₂ - M₁))).congr' ?_
    filter_upwards with k
    simp only [Function.comp_apply]
    exact plusBoxObsExpectation_index_congr (by omega) (by omega) O _ _
  rcases le_total N₁ N₂ with h | h
  · exact key hS₁ hS₂ h
  · exact (key hS₂ hS₁ h).symm

/-- **Box-independence of the `−`-state functional**: `minusStateExpectation` does not
depend on the witnessing box `N` (the `(−h, flipObs)` specialisation of
`plusStateExpectation_congr_N`). -/
theorem minusStateExpectation_congr_N {N₁ N₂ : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (O : LocalObservable d) (hS₁ : O.S ⊆ cubicBox d N₁) (hS₂ : O.S ⊆ cubicBox d N₂) :
    minusStateExpectation J h β O hS₁ = minusStateExpectation J h β O hS₂ :=
  plusStateExpectation_congr_N (h := -h) hβ hJ O.flipObs hS₁ hS₂

end Ambient

end IsingModel
