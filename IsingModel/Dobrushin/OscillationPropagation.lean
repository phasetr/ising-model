import IsingModel.Dobrushin.SiteOscillation
import IsingModel.Dobrushin.InfluenceMatrixDecay

/-!
# Oscillation propagation under the heat-bath operator (GJ §17.1, Issue #4201)

The heart of the Dobrushin comparison theorem: applying the single-site heat-bath operator `K_x`
controls the oscillation vector by the influence matrix. Precisely,
`siteOsc y (K_x f) ≤ siteOsc y f + C_{xy}·siteOsc x f`, where `C_{xy} = isingInfluence = tanh(βJ)·
[y∼x]`. At the site `x` itself the oscillation is removed (`siteOsc x (K_x f) = 0`); at another site
`y` the change in `K_x f` from flipping `y` is a convex combination of `y`-oscillations of `f`
(giving `siteOsc y f`) plus the influence of `y` on the single-site conditional at `x` times the
`x`-oscillation (giving `C_{xy}·siteOsc x f`). This is the per-step Dobrushin inequality
`d(K_x f) ≤ d(f) + C·column`, iterated over the sites of `Λ` to obtain the comparison theorem (later
PRs).

* `isingInfluence_nonneg` — `0 ≤ C_{xy}` (for `0 ≤ βJ`).
* `siteOsc_heatBath_le` — `siteOsc y (K_x f) ≤ siteOsc y f + C_{xy}·siteOsc x f`.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The two-point heat-bath difference bound** (real-number algebra): for a convex weight
`pu ∈ [0,1]`, the difference of two convex combinations is bounded by the larger spread `Oy` plus
the weight gap `c` times the spread `Ox`. The decomposition
`(pu·fu + (1−pu)·fd) − (pd·fu' + (1−pd)·fd') = pu(fu−fu') + (1−pu)(fd−fd') + (pu−pd)(fu'−fd')`. -/
private theorem heatBath_diff_abs_le_aux {pu pd fu fd fu' fd' Oy Ox c : ℝ}
    (hpu0 : 0 ≤ pu) (hpu1 : pu ≤ 1) (hfu : |fu - fu'| ≤ Oy) (hfd : |fd - fd'| ≤ Oy)
    (hfx : |fu' - fd'| ≤ Ox) (hp : |pu - pd| ≤ c) :
    |(pu * fu + (1 - pu) * fd) - (pd * fu' + (1 - pd) * fd')| ≤ Oy + c * Ox := by
  have h1mpu : 0 ≤ 1 - pu := by linarith
  have hc0 : 0 ≤ c := le_trans (abs_nonneg _) hp
  have hid : (pu * fu + (1 - pu) * fd) - (pd * fu' + (1 - pd) * fd')
      = pu * (fu - fu') + (1 - pu) * (fd - fd') + (pu - pd) * (fu' - fd') := by ring
  rw [hid]
  calc |pu * (fu - fu') + (1 - pu) * (fd - fd') + (pu - pd) * (fu' - fd')|
      ≤ |pu * (fu - fu') + (1 - pu) * (fd - fd')| + |(pu - pd) * (fu' - fd')| := abs_add_le _ _
    _ ≤ (|pu * (fu - fu')| + |(1 - pu) * (fd - fd')|) + |(pu - pd) * (fu' - fd')| := by
        gcongr; exact abs_add_le _ _
    _ = (pu * |fu - fu'| + (1 - pu) * |fd - fd'|) + |pu - pd| * |fu' - fd'| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hpu0, abs_of_nonneg h1mpu]
    _ ≤ (pu * Oy + (1 - pu) * Oy) + c * Ox := by
        apply add_le_add (add_le_add (mul_le_mul_of_nonneg_left hfu hpu0)
          (mul_le_mul_of_nonneg_left hfd h1mpu))
        exact mul_le_mul hp hfx (abs_nonneg _) hc0
    _ = Oy + c * Ox := by ring

variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

omit [Fintype G.edgeSet] in
/-- **The influence coefficient is nonnegative** (for `0 ≤ βJ`). -/
theorem isingInfluence_nonneg {β J : ℝ} (hβJ : 0 ≤ β * J) (x y : ι) :
    0 ≤ isingInfluence G β J x y := by
  rw [isingInfluence]
  split
  · exact tanh_nonneg_of_nonneg hβJ
  · exact le_refl 0

/-- **Oscillation propagation under the heat-bath operator** (GJ §17.1): for `0 ≤ βJ`,
`siteOsc y (K_x f) ≤ siteOsc y f + C_{xy}·siteOsc x f` with `C_{xy} = isingInfluence`. The per-step
Dobrushin inequality: applying the single-site heat-bath at `x` adds at most `C_{xy}` times the
`x`-oscillation to the `y`-oscillation (and removes the `x`-oscillation entirely). -/
theorem siteOsc_heatBath_le {β J : ℝ} (hβJ : 0 ≤ β * J) (h : ℝ) (x y : ι) (f : Config ι → ℝ) :
    siteOsc y (heatBath G β J h x f)
      ≤ siteOsc y f + isingInfluence G β J x y * siteOsc x f := by
  by_cases hyx : y = x
  · subst hyx
    rw [siteOsc_heatBath_self]
    exact add_nonneg (siteOsc_nonneg y f)
      (mul_nonneg (isingInfluence_nonneg G hβJ y y) (siteOsc_nonneg y f))
  · refine siteOsc_le_of_forall fun σ => ?_
    have key : ∀ s : Spin, |f (Function.update (Function.update σ y Spin.up) x s)
        - f (Function.update (Function.update σ y Spin.down) x s)| ≤ siteOsc y f := by
      intro s
      rw [Function.update_comm hyx Spin.up s σ, Function.update_comm hyx Spin.down s σ]
      exact abs_sub_update_le_siteOsc y f (Function.update σ x s)
    have hpu0 : 0 ≤ singleSiteUpProbBC G β J h x (Function.update σ y Spin.up) := by
      rw [singleSiteUpProbBC]; exact isingSingleSiteUpProb_nonneg _
    have hpu1 : singleSiteUpProbBC G β J h x (Function.update σ y Spin.up) ≤ 1 := by
      rw [singleSiteUpProbBC]; exact isingSingleSiteUpProb_le_one _
    have hag : agreesOff {y} (Function.update σ y Spin.up) (Function.update σ y Spin.down) := by
      intro i hi
      have hiy : i ≠ y := by simpa using hi
      rw [Function.update_of_ne hiy, Function.update_of_ne hiy]
    have hp : |singleSiteUpProbBC G β J h x (Function.update σ y Spin.up)
        - singleSiteUpProbBC G β J h x (Function.update σ y Spin.down)|
        ≤ isingInfluence G β J x y := by
      by_cases hyn : y ∈ G.neighborFinset x
      · rw [isingInfluence, if_pos hyn]
        exact singleSiteUpProbBC_neighbour_dist_le G hβJ h x hyn hag
      · rw [singleSiteUpProbBC_eq_of_not_neighbour G β J h x hyn hag, sub_self, abs_zero]
        exact isingInfluence_nonneg G hβJ x y
    rw [heatBath, heatBath, gibbsExpectationBC_singleton_eq, gibbsExpectationBC_singleton_eq]
    exact heatBath_diff_abs_le_aux hpu0 hpu1 (key Spin.up) (key Spin.down)
      (abs_sub_update_le_siteOsc x f (Function.update σ y Spin.down)) hp

end Dobrushin

end IsingModel
