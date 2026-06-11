import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Analytic.Basic

/-!
# Equicontinuity of uniformly bounded analytic families (GJ §4.6 Thm 4.6.2)

The general analytic layer of the Ascoli side-condition constructors (Issue #628): a family of
analytic functions on a ball, uniformly bounded there, has uniformly bounded derivatives on
interior sub-balls (Schwarz/Cauchy estimate), hence a uniform local Lipschitz estimate, hence is
pointwise equicontinuous. This discharges the `equicontinuous` field of the branch-deviation
Ascoli data from a stage-uniform closed-ball bound, with no per-stage input.

* `norm_deriv_le_of_analyticOnNhd_of_bounded` — the Schwarz-lemma derivative bound `2C/ρ`.
* `norm_sub_le_of_analyticOnNhd_of_bounded` — the uniform local Lipschitz estimate.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6, Theorem 4.6.2.
-/

namespace IsingModel

open Metric

/-- **Derivative bound for a bounded analytic function** (Schwarz): if `f` is analytic on
`ball c R` with `‖f‖ ≤ C` there, then at any `ξ` whose `ρ`-ball stays inside,
`‖deriv f ξ‖ ≤ 2C/ρ`. -/
theorem norm_deriv_le_of_analyticOnNhd_of_bounded {f : ℂ → ℂ} {c : ℂ} {R C : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball c R))
    (hb : ∀ z ∈ ball c R, ‖f z‖ ≤ C)
    {ξ : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hsub : ball ξ ρ ⊆ ball c R) :
    ‖deriv f ξ‖ ≤ 2 * C / ρ := by
  have hξmem : ξ ∈ ball c R := hsub (mem_ball_self hρ)
  have hd : DifferentiableOn ℂ f (ball ξ ρ) :=
    fun z hz => ((hf z (hsub hz)).differentiableAt).differentiableWithinAt
  have hmaps : Set.MapsTo f (ball ξ ρ) (closedBall (f ξ) (2 * C)) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    calc ‖f z - f ξ‖ ≤ ‖f z‖ + ‖f ξ‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hb z (hsub hz)) (hb ξ hξmem)
      _ = 2 * C := by ring
  exact Complex.norm_deriv_le_div_of_mapsTo_ball hd hmaps hρ

/-- **Uniform local Lipschitz estimate for a bounded analytic function**: on the half-ball
`ball z₀ (ρ/2)` inside the domain, `‖f y - f x‖ ≤ (2C/(ρ/2)) · ‖y - x‖`, with a constant
depending only on the bound `C` and the geometry — uniform over the family. -/
theorem norm_sub_le_of_analyticOnNhd_of_bounded {f : ℂ → ℂ} {c : ℂ} {R C : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball c R))
    (hb : ∀ z ∈ ball c R, ‖f z‖ ≤ C)
    {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hsub : ball z₀ ρ ⊆ ball c R)
    {x y : ℂ} (hx : x ∈ ball z₀ (ρ / 2)) (hy : y ∈ ball z₀ (ρ / 2)) :
    ‖f y - f x‖ ≤ 2 * C / (ρ / 2) * ‖y - x‖ := by
  have hhalf : ball z₀ (ρ / 2) ⊆ ball c R :=
    (ball_subset_ball (by linarith)).trans hsub
  refine Convex.norm_image_sub_le_of_norm_deriv_le
    (fun ξ hξ => (hf ξ (hhalf hξ)).differentiableAt)
    (fun ξ hξ => ?_) (convex_ball z₀ (ρ / 2)) hx hy
  have hξsub : ball ξ (ρ / 2) ⊆ ball c R := by
    refine (ball_subset_ball' ?_).trans hsub
    rw [mem_ball] at hξ
    linarith [hξ.le]
  exact norm_deriv_le_of_analyticOnNhd_of_bounded hf hb (by positivity) hξsub

end IsingModel
