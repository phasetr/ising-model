import IsingModel.Concrete.LatticeGraphCorrelation.PlusRegionExpectation
import IsingModel.Concrete.LatticeGraphCorrelation.LocalObservableState

/-!
# Cubic-radius convergence of the region `+` expectation (Issue #3581)

Towards exhaustion independence (FV §3.4 Theorem 3.17): the region `+` expectation
`plusRegionExpectation (cubicBox d r)` of a monotone local observable converges, as
the radius `r → ∞`, to the cubic-exhaustion `+`-state functional
`plusStateExpectation`.  This is the radius-reindexed form of the monotone-convergence
limit `tendsto_plusBoxLocalObservable_infiniteVolume`, packaged as a **total**
sequence `regionCubicValue` (using `max N r` so the support hypothesis always holds)
ready to be composed with the inner/outer radii of a general exhaustion.

* `plusRegionExpectation_cubicBox_antitone` — antitone in the cubic radius.
* `regionCubicValue` — the total cubic-radius region `+` expectation sequence.
* `regionCubicValue_eq` — its value for `N ≤ r`.
* `tendsto_plusRegionExpectation_cubicBox` — `N+k`-indexed convergence.
* `tendsto_regionCubicValue` — radius-reindexed convergence.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.4 Theorem 3.17 (statement p. 95, proof pp. 102–103).
-/

namespace IsingModel

namespace Ambient

open Finset Filter Topology

variable {d : ℕ}

/-- **Antitonicity in the cubic radius**: for `r₁ ≤ r₂` (both containing the support),
the region `+` expectation on the larger box is smaller (FV Lemma 3.22, since the
cubic boxes nest `cubicBox d r₁ ⊆ cubicBox d r₂`). -/
theorem plusRegionExpectation_cubicBox_antitone {r₁ r₂ : ℕ} (hr : r₁ ≤ r₂)
    {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (O : LocalMonotoneObservable d)
    (hS₁ : O.S ⊆ cubicBox d r₁) :
    plusRegionExpectation (cubicBox d r₂) J h β O (hS₁.trans (cubicBox_mono d hr))
      ≤ plusRegionExpectation (cubicBox d r₁) J h β O hS₁ :=
  plusRegionExpectation_antitone (cubicBox_mono d hr) hβ hJ O hS₁

/-- **The total cubic-radius region `+` expectation sequence**: `regionCubicValue` at
radius `r` is the region `+` expectation on `cubicBox d (max N r)`.  Using `max N r`
keeps the support hypothesis `O.S ⊆ cubicBox d (max N r)` available for every `r`, so
the sequence is total and can be composed with arbitrary radius sequences. -/
noncomputable def regionCubicValue {N : ℕ} (J h β : ℝ) (O : LocalMonotoneObservable d)
    (hS : O.S ⊆ cubicBox d N) (r : ℕ) : ℝ :=
  plusRegionExpectation (cubicBox d (max N r)) J h β O
    (hS.trans (cubicBox_mono d (le_max_left N r)))

/-- **Value of `regionCubicValue` for `N ≤ r`**: there `max N r = r`, so it is the
region `+` expectation on `cubicBox d r`. -/
theorem regionCubicValue_eq {N r : ℕ} (hNr : N ≤ r) {J h β : ℝ}
    (O : LocalMonotoneObservable d) (hS : O.S ⊆ cubicBox d N) (hSr : O.S ⊆ cubicBox d r) :
    regionCubicValue J h β O hS r = plusRegionExpectation (cubicBox d r) J h β O hSr := by
  simp only [regionCubicValue, max_eq_right hNr]

/-- **Index congruence for the cubic region `+` expectation**: equal radii give equal
values (the support hypotheses are proof-irrelevant). -/
theorem plusRegionExpectation_cubicBox_index_congr {n n' : ℕ} (hnn : n = n')
    {J h β : ℝ} (O : LocalMonotoneObservable d) (hS : O.S ⊆ cubicBox d n)
    (hS' : O.S ⊆ cubicBox d n') :
    plusRegionExpectation (cubicBox d n) J h β O hS
      = plusRegionExpectation (cubicBox d n') J h β O hS' := by
  subst hnn; rfl

/-- **`N+k`-indexed cubic-radius convergence**: the region `+` expectation on
`cubicBox d (N+k)` converges to the cubic-exhaustion `+`-state functional
`plusStateExpectation` as `k → ∞` (the region form of
`tendsto_plusBoxLocalObservable_infiniteVolume`, via
`plusRegionExpectation_cubicBox_eq`). -/
theorem tendsto_plusRegionExpectation_cubicBox {N : ℕ} {J h β : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (O : LocalMonotoneObservable d) (hS : O.S ⊆ cubicBox d N) :
    Tendsto (fun k => plusRegionExpectation (cubicBox d (N + k)) J h β O
        (hS.trans (cubicBox_mono d (Nat.le_add_right N k)))) atTop
      (nhds (plusStateExpectation J h β (⟨O.S, O.φ⟩ : LocalObservable d) hS)) := by
  rw [plusStateExpectation_of_monotone hβ hJ O hS]
  refine (tendsto_plusBoxLocalObservable_infiniteVolume hβ hJ O hS).congr (fun k => ?_)
  exact (plusRegionExpectation_cubicBox_eq O _).symm

/-- **Radius-reindexed cubic convergence**: the total sequence `regionCubicValue`
converges to the cubic-exhaustion `+`-state functional `plusStateExpectation` as the
radius `r → ∞`.  Obtained from the `N+k`-indexed convergence by the reindexing
`r ↦ r - N` (`tendsto_sub_atTop_nat`), which is cofinal at infinity. -/
theorem tendsto_regionCubicValue {N : ℕ} {J h β : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (O : LocalMonotoneObservable d) (hS : O.S ⊆ cubicBox d N) :
    Tendsto (regionCubicValue J h β O hS) atTop
      (nhds (plusStateExpectation J h β (⟨O.S, O.φ⟩ : LocalObservable d) hS)) := by
  have hbase := (tendsto_plusRegionExpectation_cubicBox (h := h) hβ hJ O hS).comp
    (tendsto_sub_atTop_nat N)
  refine hbase.congr' ?_
  filter_upwards [eventually_ge_atTop N] with r hNr
  simp only [Function.comp_apply]
  rw [regionCubicValue_eq hNr O hS (hS.trans (cubicBox_mono d hNr))]
  exact plusRegionExpectation_cubicBox_index_congr (Nat.add_sub_cancel' hNr) O _ _

end Ambient

end IsingModel
