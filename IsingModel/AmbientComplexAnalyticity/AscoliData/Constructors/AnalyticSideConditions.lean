import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.MetricSpace.Equicontinuity
import IsingModel.AmbientComplexAnalyticity.AscoliData.Structures.BranchLocallyBounded

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

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Canonical continuous restriction of a stage branch** to its selected Lee–Yang ball: the
branch is analytic on the ball (`branch_spec`), hence continuous, and the subtype restriction
is a `ContinuousMap`. -/
noncomputable def branchRestricted (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] {J β : ℂ}
    (data : LeeYangAllStageBranchData G Λ J β)
    (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) (m : ℕ) :
    C(Metric.ball (h₀ : ℂ) (data.radius h₀), ℂ) :=
  ⟨(Metric.ball (h₀ : ℂ) (data.radius h₀)).restrict (data.branchFamily h₀ m),
    ((data.branch_spec h₀ m).1.continuousOn).restrict⟩

/-- The canonical restriction agrees with the branch family. -/
theorem branchRestricted_apply (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] {J β : ℂ}
    (data : LeeYangAllStageBranchData G Λ J β)
    (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) (m : ℕ) (z : ℂ)
    (hz : z ∈ Metric.ball (h₀ : ℂ) (data.radius h₀)) :
    data.branchFamily h₀ m z = branchRestricted G Λ data h₀ m ⟨z, hz⟩ := rfl

/-- **The canonical restrictions of a stage-uniformly bounded branch family are equicontinuous
as a range carrier**: the Schwarz/Lipschitz estimates apply to the underlying analytic family,
and equicontinuity transfers to the range. -/
theorem equicontinuous_branchRestricted_range (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] {J β : ℂ}
    (data : LeeYangAllStageBranchData G Λ J β)
    (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ m, ∀ z ∈ Metric.ball (h₀ : ℂ) (data.radius h₀),
      ‖data.branchFamily h₀ m z‖ ≤ C) :
    Equicontinuous ((↑) : Set.range (branchRestricted G Λ data h₀) →
      Metric.ball (h₀ : ℂ) (data.radius h₀) → ℂ) := by
  refine equicontinuous_range_coe _ ?_
  exact equicontinuous_restrict_of_analyticOnNhd_of_bounded hC
    (fun m => (data.branch_spec h₀ m).1) hb

/-- **Closed-ball branch-deviation Ascoli data from a stage-uniform bound**: reduces the six
fields of `LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData` to four
inputs — range-image closedness, the stage-uniform norm bound, the branch-deviation bound, and
eventual overlap coherence. The continuous restrictions, the restriction identity, and the
equicontinuity are derived from the branch analyticity and the Schwarz/Lipschitz estimates. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.ofUniformBound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (closedData : LeeYangClosedBallPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K closedData.data)
    (hclosed : ∀ i : Fin geom.n, IsClosed (ContinuousMap.toFun ''
      Set.range (branchRestricted G Λ closedData.data.branchData (geom.center i))))
    (hbound : ∀ i : Fin geom.n, ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ∀ z ∈ Metric.ball
        ((geom.center i : ℂ)) (closedData.data.branchData.radius (geom.center i)),
        ‖closedData.data.branchData.branchFamily (geom.center i) m z‖ ≤ C)
    (hdev : ∀ i : Fin geom.n, ∃ D : ℝ, ∀ m z
      (_hz : z ∈ Metric.ball ((geom.center i : ℂ))
        (closedData.data.branchData.radius (geom.center i))),
      ‖closedData.data.branchData.branchFamily (geom.center i) m z
          - freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ D)
    (hover : ∀ i j : Fin geom.n, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (closedData.data.branchData.branchFamily (geom.center i) m)
        (closedData.data.branchData.branchFamily (geom.center j) m)
        (Metric.ball ((geom.center i : ℂ))
            (closedData.data.branchData.radius (geom.center i))
          ∩ Metric.ball ((geom.center j : ℂ))
            (closedData.data.branchData.radius (geom.center j)))) :
    LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
      G Λ p K closedData geom where
  restricted i := branchRestricted G Λ closedData.data.branchData (geom.center i)
  toFun_image_closed := hclosed
  branch_deviation_bound := hdev
  equicontinuous i := by
    obtain ⟨C, hC0, hCb⟩ := hbound i
    exact equicontinuous_branchRestricted_range G Λ closedData.data.branchData
      (geom.center i) hC0 hCb
  restrict_eq i m z hz :=
    branchRestricted_apply G Λ closedData.data.branchData (geom.center i) m z hz
  overlap_eventually := hover

/-- **Branch norm-bounded Ascoli data from a stage-uniform bound**: the norm-bounded variant of
`ofUniformBound` — the same three derivable fields, with the pointwise `bound` taken to be the
stage-uniform constant on each selected ball. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData.ofUniformBound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (hclosed : ∀ i : Fin geom.n, IsClosed (ContinuousMap.toFun ''
      Set.range (branchRestricted G Λ data.branchData (geom.center i))))
    (hbound : ∀ i : Fin geom.n, ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ∀ z ∈ Metric.ball
        ((geom.center i : ℂ)) (data.branchData.radius (geom.center i)),
        ‖data.branchData.branchFamily (geom.center i) m z‖ ≤ C)
    (hover : ∀ i j : Fin geom.n, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (geom.center i) m)
        (data.branchData.branchFamily (geom.center j) m)
        (Metric.ball ((geom.center i : ℂ)) (data.branchData.radius (geom.center i))
          ∩ Metric.ball ((geom.center j : ℂ))
            (data.branchData.radius (geom.center j)))) :
    LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData
      G Λ p K data geom where
  restricted i := branchRestricted G Λ data.branchData (geom.center i)
  bound i := fun _ => (hbound i).choose
  toFun_image_closed := hclosed
  branch_norm_le i m z hz := (hbound i).choose_spec.2 m z hz
  equicontinuous i :=
    equicontinuous_branchRestricted_range G Λ data.branchData (geom.center i)
      (hbound i).choose_spec.1 (hbound i).choose_spec.2
  restrict_eq i m z hz :=
    branchRestricted_apply G Λ data.branchData (geom.center i) m z hz
  overlap_eventually := hover

end Ambient

end IsingModel
