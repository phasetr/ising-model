import IsingModel.Dobrushin.HeatBathInvariance

/-!
# The single-site oscillation of an observable (GJ §17.1, Issue #4201)

The **Dobrushin single-site oscillation** of an observable `f` at a site `x` is
`siteOsc x f = sup_σ |f(σ[x↦↑]) − f(σ[x↦↓])|` — the largest change in `f` from flipping the spin at
`x` (over all configurations of the other sites). This is the quantity propagated by the heat-bath
operator in the Dobrushin comparison theorem: the oscillation vector `(siteOsc x f)_x` is controlled
by the influence matrix `C` and the boundary data (later PRs). Two basic facts feed the telescoping:
the per-configuration bound `|f(σ[x↦↑]) − f(σ[x↦↓])| ≤ siteOsc x f`, and that the heat-bath operator
`K_x` removes the oscillation at its own site (`siteOsc x (K_x f) = 0`).

* `siteOsc` — the single-site oscillation.
* `siteOsc_nonneg` / `abs_sub_update_le_siteOsc` / `siteOsc_le_of_forall`.
* `siteOsc_heatBath_self` — `siteOsc x (K_x f) = 0`.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The single-site oscillation** of `f` at `x`: the maximum, over all configurations `σ`, of the
change in `f` from setting the spin at `x` to `up` versus `down`. -/
noncomputable def siteOsc (x : ι) (f : Config ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun σ => |f (Function.update σ x Spin.up) - f (Function.update σ x Spin.down)|)

/-- **The per-configuration single-site change is at most the oscillation**. -/
theorem abs_sub_update_le_siteOsc (x : ι) (f : Config ι → ℝ) (σ : Config ι) :
    |f (Function.update σ x Spin.up) - f (Function.update σ x Spin.down)| ≤ siteOsc x f :=
  Finset.le_sup'
    (fun σ => |f (Function.update σ x Spin.up) - f (Function.update σ x Spin.down)|)
    (Finset.mem_univ σ)

/-- **The single-site oscillation is nonnegative**. -/
theorem siteOsc_nonneg (x : ι) (f : Config ι → ℝ) : 0 ≤ siteOsc x f :=
  le_trans (abs_nonneg _) (abs_sub_update_le_siteOsc x f (Classical.arbitrary _))

/-- **Upper bound for the oscillation from a uniform per-configuration bound**. -/
theorem siteOsc_le_of_forall {x : ι} {f : Config ι → ℝ} {c : ℝ}
    (h : ∀ σ : Config ι,
      |f (Function.update σ x Spin.up) - f (Function.update σ x Spin.down)| ≤ c) :
    siteOsc x f ≤ c :=
  Finset.sup'_le _ _ fun σ _ => h σ

variable (G : SimpleGraph ι) [Fintype G.edgeSet]

/-- **The heat-bath operator removes the oscillation at its own site**: `siteOsc x (K_x f) = 0`,
since `K_x f` does not depend on the spin at `x` (the single-site conditional ignores the boundary
value at `x`). -/
theorem siteOsc_heatBath_self (β J h : ℝ) (x : ι) (f : Config ι → ℝ) :
    siteOsc x (heatBath G β J h x f) = 0 := by
  refine le_antisymm (siteOsc_le_of_forall fun σ => ?_) (siteOsc_nonneg x _)
  have hup : heatBath G β J h x f (Function.update σ x Spin.up)
      = gibbsExpectationBC G β (fun _ => J) h {x} σ f :=
    gibbsExpectationBC_singleton_boundary_update G β J h x Spin.up σ f
  have hdn : heatBath G β J h x f (Function.update σ x Spin.down)
      = gibbsExpectationBC G β (fun _ => J) h {x} σ f :=
    gibbsExpectationBC_singleton_boundary_update G β J h x Spin.down σ f
  rw [hup, hdn, sub_self, abs_zero]

end Dobrushin

end IsingModel
