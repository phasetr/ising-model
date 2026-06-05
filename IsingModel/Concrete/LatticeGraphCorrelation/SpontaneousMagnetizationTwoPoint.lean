import IsingModel.Concrete.LatticeGraphCorrelation.PlusTwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationSiteIndependence
import IsingModel.Concrete.LatticeGraphCorrelation.SpontaneousMagnetization
import IsingModel.Inequalities.GKSBoundaryConditionTwoPoint

/-!
# Clustering bound `m*² ≤ μ⁺(σ₀σₓ)` (FV §3.7, Issue #3613)

The squared spontaneous magnetization is bounded by the infinite-volume `+` two-point
function: `m*² ≤ μ⁺(σ₀σₓ)`.  This is the GKS-II clustering bound taken to the
infinite-volume limit (finite-box `⟨σ₀⟩⁺⟨σₓ⟩⁺ ≤ ⟨σ₀σₓ⟩⁺` + the box-aligned limit,
using site-independence for `⟨σₓ⟩⁺ = m*`).

* `tendsto_plusMagnetization_atRadius` — the single-spin box convergence at any box
  radius `M ≥ latticeRadius x`.
* `plusBoxObsExpectation_two_point_clustering` — the finite-box clustering.
* `plusStateSpontaneousMagnetization_sq_le_plusTwoPoint` — `m*² ≤ μ⁺(σ₀σₓ)`.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.
-/

namespace IsingModel

namespace Ambient

open Finset Filter Topology

variable {d : ℕ}

/-- **Single-spin box convergence at an arbitrary box radius** `M ≥ latticeRadius x`:
the `+` box expectation of the single spin at `x`, computed on the boxes
`cubicBox d (M + k + 1)`, converges to `m⁺(x)` (box-independence of the limit). -/
theorem tendsto_plusMagnetization_atRadius {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (M : ℕ) (x : Fin d → ℤ) (hMx : latticeRadius x ≤ M) :
    Tendsto (fun k => plusBoxObsExpectation (M + k) (M + k + 1) J h β
        (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d)
        (((singleSpinMonoObs_support_subset x).trans (cubicBox_mono d hMx)).trans
          (cubicBox_mono d (by omega : M ≤ M + k + 1)))) atTop
      (nhds (plusMagnetization x J h β)) := by
  have hSM : (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d).S ⊆
      cubicBox d M := (singleSpinMonoObs_support_subset x).trans (cubicBox_mono d hMx)
  have h1 := tendsto_plusStateExpectation (N := M) (h := h) hβ hJ
    (⟨(singleSpinMonoObs x).S, (singleSpinMonoObs x).φ⟩ : LocalObservable d) hSM
  rwa [plusStateExpectation_congr_N hβ hJ _ hSM (singleSpinMonoObs_support_subset x)] at h1

/-- **Finite-box two-point clustering**: for `i ≠ j`, the product of the single-spin
`+` box expectations is bounded by the two-spin `+` box expectation. -/
theorem plusBoxObsExpectation_two_point_clustering (n m : ℕ) {J β : ℝ} (hβ : 0 < β)
    (hJ : 0 ≤ J) {i j : Fin d → ℤ} (hij : i ≠ j)
    (hSi : (⟨(singleSpinMonoObs i).S, (singleSpinMonoObs i).φ⟩ : LocalObservable d).S ⊆
      cubicBox d m)
    (hSj : (⟨(singleSpinMonoObs j).S, (singleSpinMonoObs j).φ⟩ : LocalObservable d).S ⊆
      cubicBox d m)
    (hSij : (twoSpinObs i j).S ⊆ cubicBox d m) :
    plusBoxObsExpectation n m J 0 β
        (⟨(singleSpinMonoObs i).S, (singleSpinMonoObs i).φ⟩ : LocalObservable d) hSi *
      plusBoxObsExpectation n m J 0 β
        (⟨(singleSpinMonoObs j).S, (singleSpinMonoObs j).φ⟩ : LocalObservable d) hSj ≤
      plusBoxObsExpectation n m J 0 β (twoSpinObs i j) hSij := by
  rw [plusBoxObsExpectation_singleSpin_eq, plusBoxObsExpectation_singleSpin_eq,
    plusBoxObsExpectation_twoSpin_eq n m hij hSij]
  exact gibbsExpectationBC_plus_two_point_ge_product _ hβ hJ le_rfl _
    (fun hc => hij (Subtype.ext_iff.mp hc))

/-- **Clustering bound** `m*² ≤ μ⁺(σ₀σₓ)`: the squared spontaneous magnetization is
bounded by the infinite-volume `+` two-point function (GKS-II clustering, in the limit,
with site-independence `m⁺(x) = m*`). -/
theorem plusStateSpontaneousMagnetization_sq_le_plusTwoPoint {J β : ℝ} (hβ : 0 < β)
    (hJ : 0 ≤ J) (x : Fin d → ℤ) (hx : x ≠ 0) :
    plusStateSpontaneousMagnetization d J β ^ 2 ≤ plusTwoPoint 0 x J 0 β := by
  set M := latticeRadius (0 : Fin d → ℤ) + latticeRadius x with hMdef
  have hM0 : latticeRadius (0 : Fin d → ℤ) ≤ M := by rw [hMdef]; omega
  have hMx : latticeRadius x ≤ M := by rw [hMdef]; omega
  have hm0 := tendsto_plusMagnetization_atRadius (h := 0) hβ.le hJ M 0 hM0
  have hmx := tendsto_plusMagnetization_atRadius (h := 0) hβ.le hJ M x hMx
  have hxeq : plusMagnetization x J 0 β = plusMagnetization (0 : Fin d → ℤ) J 0 β := by
    have hv : plusMagnetization (x +ᵥ (0 : Fin d → ℤ)) J 0 β
        = plusMagnetization (0 : Fin d → ℤ) J 0 β :=
      plusMagnetization_vadd hβ.le hJ x 0
    simpa [vadd_eq_add] using hv
  have hmul := hm0.mul hmx
  rw [hxeq] at hmul
  have hlim : plusMagnetization (0 : Fin d → ℤ) J 0 β * plusMagnetization (0 : Fin d → ℤ) J 0 β
      = plusStateSpontaneousMagnetization d J β ^ 2 := by
    rw [plusStateSpontaneousMagnetization, pow_two]
  rw [hlim] at hmul
  have hpair := tendsto_plusTwoPoint (h := 0) hβ.le hJ 0 x
  refine le_of_tendsto_of_tendsto' hmul hpair (fun k => ?_)
  exact plusBoxObsExpectation_two_point_clustering _ _ hβ hJ (fun hc => hx hc.symm) _ _ _

end Ambient

end IsingModel
