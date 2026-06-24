import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Equicontinuity

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

/-- **Equicontinuity at a point from a local uniform bound** (Montel input, ball form).

If every `F n` is holomorphic on the open `U`, `ball x₀ ρ ⊆ U` (`ρ > 0`), and `‖F n w‖ ≤ M` for all
`n` and `w ∈ ball x₀ ρ`, then the family `F` is equicontinuous at `x₀`.

Proof: on `closedBall x₀ (ρ/2) ⊆ ball x₀ ρ` every `F n` is bounded by `M`, so by
`lipschitzBound_of_bounded_on_closedBall` every `F n` is `(M/(ρ/4))`-Lipschitz on the inner disc
`closedBall x₀ (ρ/4)` — a common modulus of continuity, which is exactly equicontinuity at `x₀`. -/
theorem equicontinuousAt_of_ball_bound
    {U : Set ℂ} (hU : IsOpen U) {F : ℕ → ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    {x₀ : ℂ} {ρ M : ℝ} (hρ : 0 < ρ) (hballU : ball x₀ ρ ⊆ U)
    (hbound : ∀ n, ∀ w ∈ ball x₀ ρ, ‖F n w‖ ≤ M) :
    EquicontinuousAt (fun n => F n) x₀ := by
  -- Geometry: inner radius `ρ/4 < ρ/2`, and `closedBall x₀ (ρ/2) ⊆ ball x₀ ρ ⊆ U`.
  have hhalf_lt : ρ / 2 < ρ := by linarith
  have hquart_lt : ρ / 4 < ρ / 2 := by linarith
  have hCB_sub : closedBall x₀ (ρ / 2) ⊆ ball x₀ ρ :=
    Metric.closedBall_subset_ball hhalf_lt
  have hCB_U : closedBall x₀ (ρ / 2) ⊆ U := hCB_sub.trans hballU
  have hbound_CB : ∀ n, ∀ w ∈ closedBall x₀ (ρ / 2), ‖F n w‖ ≤ M :=
    fun n w hw => hbound n w (hCB_sub hw)
  -- The common Lipschitz constant `L = M / (ρ/2 − ρ/4) = M / (ρ/4) = 4M/ρ`.
  set L : ℝ := M / (ρ / 2 - ρ / 4) with hL_def
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hbound 0 x₀ (Metric.mem_ball_self hρ))
  have hden : 0 < ρ / 2 - ρ / 4 := by linarith
  have hL0 : 0 ≤ L := div_nonneg hM0 hden.le
  -- Uniform Lipschitz bound on the inner disc.
  have hLip : ∀ n, ∀ x ∈ closedBall x₀ (ρ / 4), ∀ x' ∈ closedBall x₀ (ρ / 4),
      ‖F n x - F n x'‖ ≤ L * ‖x - x'‖ := by
    intro n x hx x' hx'
    exact lipschitzBound_of_bounded_on_closedBall hU (hF n) hquart_lt hCB_U (hbound_CB n) hx hx'
  -- Convert the common modulus into equicontinuity at `x₀`.
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  refine ⟨min (ρ / 4) (ε / (L + 1)), lt_min (by linarith) (by positivity), ?_⟩
  intro x hx n
  have hx_in : x ∈ closedBall x₀ (ρ / 4) := by
    rw [Metric.mem_closedBall]
    exact le_of_lt (lt_of_lt_of_le hx (min_le_left _ _))
  have hx₀_in : x₀ ∈ closedBall x₀ (ρ / 4) := Metric.mem_closedBall_self (by linarith)
  have hbnd := hLip n x₀ hx₀_in x hx_in
  -- `dist (F n x₀) (F n x) = ‖F n x₀ − F n x‖ ≤ L * ‖x₀ − x‖ = L * dist x x₀`.
  rw [dist_eq_norm]
  calc ‖F n x₀ - F n x‖ ≤ L * ‖x₀ - x‖ := hbnd
    _ = L * dist x x₀ := by rw [← dist_eq_norm, dist_comm]
    _ < ε := by
        have hdistlt : dist x x₀ < ε / (L + 1) :=
          lt_of_lt_of_le hx (min_le_right _ _)
        have hLp1 : 0 < L + 1 := by linarith
        calc L * dist x x₀ ≤ (L + 1) * dist x x₀ := by
              apply mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
          _ < (L + 1) * (ε / (L + 1)) :=
              mul_lt_mul_of_pos_left hdistlt hLp1
          _ = ε := by field_simp

/-- **Equicontinuity at a point from the local-boundedness hypothesis** (Montel input).

Existential-`ball` repackaging of `equicontinuousAt_of_ball_bound`: from the local uniform bound
`∃ r M, 0 < r ∧ ball x₀ r ⊆ U ∧ ∀ n w ∈ ball x₀ r, ‖F n w‖ ≤ M` (the standard "locally uniformly
bounded family" hypothesis at `x₀`), the holomorphic family `F` is equicontinuous at `x₀`. -/
theorem equicontinuousAt_of_locallyBounded
    {U : Set ℂ} (hU : IsOpen U) {F : ℕ → ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U) {x₀ : ℂ}
    (hbdd : ∃ r M : ℝ, 0 < r ∧ ball x₀ r ⊆ U ∧ ∀ n, ∀ w ∈ ball x₀ r, ‖F n w‖ ≤ M) :
    EquicontinuousAt (fun n => F n) x₀ := by
  obtain ⟨r, M, hr, hrU, hbound⟩ := hbdd
  exact equicontinuousAt_of_ball_bound hU hF hr hrU hbound

end FunctionTheory
end IsingModel
