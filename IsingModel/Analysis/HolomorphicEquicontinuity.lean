import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Equicontinuity of uniformly bounded holomorphic families (shared Montel/Ascoli core)

Common analysis core for the two Montel-type equicontinuity arguments used in the project
(Issue #4501): a family of holomorphic functions on a ball, uniformly bounded there, has
uniformly bounded derivatives on interior sub-balls (Schwarz/Cauchy estimate), hence a uniform
local Lipschitz estimate, hence is equicontinuous. Both the Ascoli side-condition constructors
(`AmbientComplexAnalyticity.AscoliData.Constructors.AnalyticSideConditions`) and the Vitali–Porter
Montel input (`ComplexAnalyticity.VitaliPorter.Equicontinuity`) are thin wrappers over the lemmas
below; the latter converts its `DifferentiableOn` hypothesis to `AnalyticOnNhd` via
`DifferentiableOn.analyticOnNhd` (holomorphic ⟹ analytic on ℂ).

* `norm_deriv_le_of_analyticOnNhd_of_bounded` — the Schwarz-lemma derivative bound `2C/ρ`.
* `norm_sub_le_of_analyticOnNhd_of_bounded` — the uniform local Lipschitz estimate.
* `equicontinuous_restrict_of_analyticOnNhd_of_bounded` — subtype-ball `Equicontinuous` form.
* `equicontinuous_range_coe` — transfer of equicontinuity to a range carrier.
* `equicontinuousAt_of_analyticOnNhd_of_ballBound` — ambient pointwise `EquicontinuousAt` form.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6,
Theorem 4.6.2; Conway, *Functions of One Complex Variable I*, VII §2
(normal families / Montel).
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
`ball z₀ (ρ/2)` inside the domain,
`‖f y - f x‖ ≤ (2C/(ρ/2)) · ‖y - x‖`, with a constant depending only on
the bound `C` and the geometry — uniform over the family. -/
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

/-- **Pointwise equicontinuity of a uniformly bounded analytic family on a ball**: the uniform
local Lipschitz estimate gives equicontinuity at every interior point, with no boundary-uniform
control. Stated on the subtype ball, matching the Ascoli-data range carriers. -/
theorem equicontinuous_restrict_of_analyticOnNhd_of_bounded {ι : Type*} {F : ι → ℂ → ℂ}
    {c : ℂ} {R C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ i, AnalyticOnNhd ℂ (F i) (ball c R))
    (hb : ∀ i, ∀ z ∈ ball c R, ‖F i z‖ ≤ C) :
    Equicontinuous (fun i (z : ball c R) => F i (z : ℂ)) := by
  intro x₀
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨z₀, hz₀⟩ := x₀
  set ρ : ℝ := R - dist z₀ c with hρdef
  have hz₀' : dist z₀ c < R := mem_ball.mp hz₀
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  have hsubρ : ball z₀ ρ ⊆ ball c R := by
    intro w hw
    rw [mem_ball] at hw ⊢
    calc dist w c ≤ dist w z₀ + dist z₀ c := dist_triangle _ _ _
      _ < ρ + dist z₀ c := by linarith
      _ = R := by rw [hρdef]; ring
  set M : ℝ := 2 * C / (ρ / 2) with hMdef
  have hM0 : 0 ≤ M := by positivity
  refine ⟨min (ρ / 2) (ε / (M + 1)), by positivity, ?_⟩
  intro x hx i
  have hd : dist (x : ℂ) z₀ < min (ρ / 2) (ε / (M + 1)) := by
    rw [Subtype.dist_eq] at hx
    exact hx
  have hxball : (x : ℂ) ∈ ball z₀ (ρ / 2) :=
    mem_ball.mpr (lt_of_lt_of_le hd (min_le_left _ _))
  have hz₀ball : z₀ ∈ ball z₀ (ρ / 2) := mem_ball_self (by positivity)
  have hlip := norm_sub_le_of_analyticOnNhd_of_bounded (hf i) (hb i) hρ hsubρ
    hxball hz₀ball
  rw [dist_eq_norm]
  calc ‖F i z₀ - F i (x : ℂ)‖ ≤ M * ‖z₀ - (x : ℂ)‖ := hlip
    _ ≤ M * (ε / (M + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hM0
        rw [← dist_eq_norm, dist_comm]
        exact le_of_lt (lt_of_lt_of_le hd (min_le_right _ _))
    _ < ε := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < M + 1)]
        nlinarith

/-- **Equicontinuity transfers to the range carrier**: the coercion family indexed by the range
of a map into continuous maps is a re-indexing of the underlying family. -/
theorem equicontinuous_range_coe {X : Type*} [TopologicalSpace X] {ι : Type*}
    (Φ : ι → C(X, ℂ)) (h : Equicontinuous (fun i => (Φ i : X → ℂ))) :
    Equicontinuous ((↑) : Set.range Φ → X → ℂ) := by
  classical
  have hcomp := h.comp (fun g : Set.range Φ => g.2.choose)
  have heq : ((fun i => (Φ i : X → ℂ)) ∘ (fun g : Set.range Φ => g.2.choose))
      = ((↑) : Set.range Φ → X → ℂ) := by
    funext g
    simp only [Function.comp_apply]
    rw [g.2.choose_spec]
  rwa [heq] at hcomp

/-- **Ambient pointwise equicontinuity of a uniformly bounded analytic family**
(Montel input, ball form): if every `F i` is analytic on `ball x₀ ρ` (`ρ > 0`)
and uniformly bounded by `M ≥ 0` there, then the family `F` is equicontinuous
at the centre `x₀` as maps on the ambient space `ℂ`.

Proof: the uniform local Lipschitz estimate
`norm_sub_le_of_analyticOnNhd_of_bounded` on the inner ball `ball x₀ (ρ/2)`
gives a common Lipschitz constant `2M/(ρ/2)`, which is a common modulus of
continuity at `x₀`. -/
theorem equicontinuousAt_of_analyticOnNhd_of_ballBound {ι : Type*} {F : ι → ℂ → ℂ}
    {x₀ : ℂ} {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) (ball x₀ ρ))
    (hbound : ∀ i, ∀ w ∈ ball x₀ ρ, ‖F i w‖ ≤ M) :
    EquicontinuousAt (fun i => F i) x₀ := by
  have hsub : ball x₀ ρ ⊆ ball x₀ ρ := subset_rfl
  set L : ℝ := 2 * M / (ρ / 2) with hL_def
  have hL0 : 0 ≤ L := by rw [hL_def]; positivity
  have hLip : ∀ i, ∀ x ∈ ball x₀ (ρ / 2), ∀ x' ∈ ball x₀ (ρ / 2),
      ‖F i x' - F i x‖ ≤ L * ‖x' - x‖ := by
    intro i x hx x' hx'
    rw [hL_def]
    exact norm_sub_le_of_analyticOnNhd_of_bounded (hF i) (hbound i) hρ hsub hx hx'
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  refine ⟨min (ρ / 2) (ε / (L + 1)), lt_min (by linarith) (by positivity), ?_⟩
  intro x hx i
  have hx_in : x ∈ ball x₀ (ρ / 2) := mem_ball.mpr (lt_of_lt_of_le hx (min_le_left _ _))
  have hx₀_in : x₀ ∈ ball x₀ (ρ / 2) := mem_ball_self (by linarith)
  have hbnd := hLip i x hx_in x₀ hx₀_in
  rw [dist_eq_norm]
  calc ‖F i x₀ - F i x‖ ≤ L * ‖x₀ - x‖ := hbnd
    _ = L * dist x x₀ := by rw [← dist_eq_norm, dist_comm]
    _ < ε := by
        have hdistlt : dist x x₀ < ε / (L + 1) := lt_of_lt_of_le hx (min_le_right _ _)
        have hLp1 : 0 < L + 1 := by linarith
        calc L * dist x x₀ ≤ (L + 1) * dist x x₀ :=
              mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
          _ < (L + 1) * (ε / (L + 1)) := mul_lt_mul_of_pos_left hdistlt hLp1
          _ = ε := by field_simp

end IsingModel
