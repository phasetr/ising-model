import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeMagnetization
import IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationBetaMonotone

/-!
# Infinite-volume `+` two-point function `μ⁺(σ_i σ_j)` (FV §3.7, Issue #3613)

The cubic-exhaustion `+`-state two-point function `μ⁺(σ_i σ_j) = plusStateExpectation`
of the two-spin product observable, with the finite-volume bridge to the spin-product
correlation and the convergence of the screened box two-point expectations.

* `twoSpinObs` — the two-spin product observable at sites `i, j`.
* `plusBoxObsExpectation_twoSpin_eq` — the finite-volume bridge.
* `plusTwoPoint` — `μ⁺(σ_i σ_j)`.
* `tendsto_plusTwoPoint` — the finite-volume convergence.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.
-/

namespace IsingModel

namespace Ambient

open Finset Filter Topology

variable {d : ℕ}

/-- **The two-spin product observable** at sites `i, j`: support `{i, j}` and function
`σ ↦ s(σ_i)·s(σ_j)`. -/
noncomputable def twoSpinObs (i j : Fin d → ℤ) : LocalObservable d :=
  ⟨{i, j}, fun σ => Spin.sign ℝ (σ ⟨i, Finset.mem_insert_self i {j}⟩) *
    Spin.sign ℝ (σ ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self j)⟩)⟩

/-- The two-spin support sits inside the cubic box of the combined lattice radii. -/
theorem twoSpinObs_support_subset (i j : Fin d → ℤ) :
    (twoSpinObs i j).S ⊆ cubicBox d (latticeRadius i + latticeRadius j) := by
  intro a ha
  rw [twoSpinObs] at ha
  rcases Finset.mem_insert.mp ha with rfl | ha'
  · exact cubicBox_mono d (Nat.le_add_right _ _) (mem_cubicBox_latticeRadius a)
  · rw [Finset.mem_singleton] at ha'
    subst ha'
    exact cubicBox_mono d (Nat.le_add_left _ _) (mem_cubicBox_latticeRadius a)

/-- **The finite-volume two-spin bridge**: the `+` box expectation of the two-spin
product equals the `+` boundary spin-product correlation `⟨σ_{⟨i⟩} σ_{⟨j⟩}⟩` on the
cubic ambient (`Spin.sign = ↑toSign`, `Finset.prod_pair`, `restrictConfig`). -/
theorem plusBoxObsExpectation_twoSpin_eq (n m : ℕ) {J h β : ℝ} {i j : Fin d → ℤ}
    (hij : i ≠ j) (hS : (twoSpinObs i j).S ⊆ cubicBox d m) :
    plusBoxObsExpectation n m J h β (twoSpinObs i j) hS
      = gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d m)) β
          (fun _ => J) h (plusBoxInterior d n m) (plusConfig _)
          (spinProduct {⟨i, hS (Finset.mem_insert_self i {j})⟩,
            ⟨j, hS (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))⟩}) := by
  unfold plusBoxObsExpectation plusBoxExpectation
  congr 1
  funext σ
  rw [spinProduct, Finset.prod_pair (by
    intro hcon; exact hij (Subtype.ext_iff.mp hcon))]
  rfl

/-- **The infinite-volume `+` two-point function** `μ⁺(σ_i σ_j)`: the cubic-exhaustion
`+`-state expectation of the two-spin product. -/
noncomputable def plusTwoPoint (i j : Fin d → ℤ) (J h β : ℝ) : ℝ :=
  plusStateExpectation J h β (twoSpinObs i j) (twoSpinObs_support_subset i j)

/-- **Convergence of the finite-volume `+` two-point function**: the screened two-spin
`+` box expectations converge to `μ⁺(σ_i σ_j)`. -/
theorem tendsto_plusTwoPoint {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (i j : Fin d → ℤ) :
    Tendsto (fun k => plusBoxObsExpectation
        (latticeRadius i + latticeRadius j + k)
        (latticeRadius i + latticeRadius j + k + 1) J h β (twoSpinObs i j)
        ((twoSpinObs_support_subset i j).trans
          (cubicBox_mono d (by omega : latticeRadius i + latticeRadius j ≤
            latticeRadius i + latticeRadius j + k + 1)))) atTop
      (nhds (plusTwoPoint i j J h β)) :=
  tendsto_plusStateExpectation hβ hJ (twoSpinObs i j) (twoSpinObs_support_subset i j)

end Ambient

end IsingModel
