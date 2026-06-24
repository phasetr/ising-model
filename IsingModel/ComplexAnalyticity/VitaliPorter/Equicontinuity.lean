import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Vitali–Porter: Montel equicontinuity from local boundedness (Cauchy estimates)

Second building block of the in-project proof eliminating the declared scope-excluded axiom
`vitaliPorter_tendstoLocallyUniformlyOn` (Issue #4280). It supplies the **Montel** half's
equicontinuity input: a holomorphic function bounded by `M` on a closed disc is, on a strictly
smaller concentric disc, Lipschitz with constant `M / (R − r)` — *uniformly in the bound*, so a
locally uniformly bounded family is locally equicontinuous.

The two key facts are pure complex analysis:
- `cauchy_norm_deriv_le`: the Cauchy derivative estimate `‖deriv f z‖ ≤ M / r` from a sup bound on
  the circle (via `Complex.cderiv_eq_deriv` + `Complex.norm_cderiv_le`).
- `lipschitzBound_of_bounded_on_closedBall`: the uniform Lipschitz bound on the inner disc (Cauchy
  estimate at every inner point + the convex mean-value inequality
  `Convex.norm_image_sub_le_of_norm_fderiv_le`).

**Reference:** Conway, *Functions of One Complex Variable I*, VII §2 (normal families / Montel). -/

namespace IsingModel
namespace FunctionTheory

open Complex Metric Set

/-- **Cauchy derivative estimate**: if `f` is holomorphic on an open `U`, `closedBall z r ⊆ U`
(`r > 0`), and `‖f w‖ ≤ M` on the circle `sphere z r`, then `‖deriv f z‖ ≤ M / r`.

Direct from `Complex.cderiv_eq_deriv` (the circle integral equals the derivative under the Cauchy
formula) and `Complex.norm_cderiv_le`. -/
theorem cauchy_norm_deriv_le
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    {z : ℂ} {r M : ℝ} (hr : 0 < r) (hball : closedBall z r ⊆ U)
    (hbound : ∀ w ∈ sphere z r, ‖f w‖ ≤ M) :
    ‖deriv f z‖ ≤ M / r := by
  rw [← Complex.cderiv_eq_deriv hU hf hr hball]
  exact Complex.norm_cderiv_le hr hbound

/-- **Uniform Lipschitz bound on the inner disc from a sup bound on the outer disc**.

If `f` is holomorphic on an open `U`, `closedBall z₀ R ⊆ U`, `‖f w‖ ≤ M` on `closedBall z₀ R`, and
`0 < r < R`, then for all `w, w' ∈ closedBall z₀ r`,
`‖f w − f w'‖ ≤ (M / (R − r)) · ‖w − w'‖`.

The Lipschitz constant `M / (R − r)` depends only on `M, R, r` (not on `f`), so a family of
holomorphic functions sharing the bound `M` is uniformly Lipschitz — hence locally equicontinuous —
on the inner disc. Proof: at each inner point `x` the Cauchy estimate on the radius-`(R−r)` circle
(contained in `closedBall z₀ R`) gives `‖deriv f x‖ ≤ M / (R − r)`; the convex mean-value inequality
`Convex.norm_image_sub_le_of_norm_fderiv_le` then yields the Lipschitz bound on the convex inner
disc. -/
theorem lipschitzBound_of_bounded_on_closedBall
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    {z₀ : ℂ} {R r M : ℝ} (hrR : r < R)
    (hball : closedBall z₀ R ⊆ U) (hbound : ∀ w ∈ closedBall z₀ R, ‖f w‖ ≤ M)
    {w w' : ℂ} (hw : w ∈ closedBall z₀ r) (hw' : w' ∈ closedBall z₀ r) :
    ‖f w - f w'‖ ≤ M / (R - r) * ‖w - w'‖ := by
  have hRr : 0 < R - r := by linarith
  -- Derivative bound at every inner point `x`.
  have hderiv : ∀ x ∈ closedBall z₀ r, ‖deriv f x‖ ≤ M / (R - r) := by
    intro x hx
    have hx_le : dist x z₀ ≤ r := by simpa [Metric.mem_closedBall] using hx
    -- `closedBall x (R − r) ⊆ closedBall z₀ R ⊆ U`.
    have hxball : closedBall x (R - r) ⊆ closedBall z₀ R :=
      Metric.closedBall_subset_closedBall' (by linarith [hx_le])
    have hxU : closedBall x (R - r) ⊆ U := hxball.trans hball
    have hsphere : ∀ y ∈ sphere x (R - r), ‖f y‖ ≤ M := by
      intro y hy
      exact hbound y (hxball (Metric.sphere_subset_closedBall hy))
    exact cauchy_norm_deriv_le hU hf hRr hxU hsphere
  -- Convex mean-value inequality on the inner disc.
  have hconv : Convex ℝ (closedBall z₀ r) := convex_closedBall z₀ r
  have hdiff : ∀ x ∈ closedBall z₀ r, DifferentiableAt ℂ f x := by
    intro x hx
    have hxU : x ∈ U := hball (Metric.closedBall_subset_closedBall (by linarith) hx)
    exact hf.differentiableAt (hU.mem_nhds hxU)
  have hfd : ∀ x ∈ closedBall z₀ r, ‖fderiv ℂ f x‖ ≤ M / (R - r) := by
    intro x hx
    rw [← norm_deriv_eq_norm_fderiv]
    exact hderiv x hx
  exact hconv.norm_image_sub_le_of_norm_fderiv_le hdiff hfd hw' hw

end FunctionTheory
end IsingModel
