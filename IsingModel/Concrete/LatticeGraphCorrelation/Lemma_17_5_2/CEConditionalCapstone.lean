import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CapstoneIncrementFromComplexBound
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.IncrementCapstone
import IsingModel.AmbientComplexAnalyticity.VolumeUniformHZ
import IsingModel.ComplexAnalyticity.SecondMomentBounds

/-!
# Lemma 17.5.2: conditional capstone via the CE route (centred at `β = 0`)

This module composes the volume-uniform `Z_ℂ ≠ 0` bridge from
`AmbientComplexAnalyticity/VolumeUniformHZ.lean` (Issue #3054) with the
capstone-coordinate conditional reduction
`dist_deriv_correlationAlongExhaustion_le_of_complex_circle_bound` (PR #3032,
`CapstoneIncrementFromComplexBound.lean`) to produce the Lemma 17.5.2
β-derivative increment bound at the centred parameter `β = 0`.

The composition takes three structural inputs:

1. `VolumeUniformZComplexIdentity (latticeGraph d) Λ J` — the polymer
   high-temperature factorisation holds on a uniform complex disc across all
   stages.
2. `VolumeUniformComplexHTBound (latticeGraph d) Λ J` — the polymer-expansion
   RHS norm is bounded below uniformly across stages.
3. A volume-uniform complex circle bound `B` on the value increment for the
   relevant pair `{x, z}` (the `hB` input to #3032).

The result is the increment bound `dist(∂_β c_k, ∂_β c_{k+1}) ≤ B/R` at
`β = 0` for every covered stage `k`, the per-stage scalar input to the
Lemma 17.5.2 capstone increment infrastructure.

The two volume-uniform CE inputs (1)-(2) remain open (complex cluster-expansion
convergence, research-level); a centred circle bound on the correlation value
increment (3) is the parallel open input from the Simon-Lieb hB side
(Issue #3044).
-/

namespace IsingModel
namespace Ambient

open Complex Metric

/-- **Lemma 17.5.2 conditional dist-increment via the CE route at `β = 0`**
(Issue #3054). Composes the volume-uniform `Z_ℂ ≠ 0` bridge
`partitionFunctionComplex_inducedGraph_ne_zero_on_ball_at_zero_of_volume_uniform`
with the capstone-coordinate conditional reduction
`dist_deriv_correlationAlongExhaustion_le_of_complex_circle_bound` (PR #3032).

For each covered stage `k` (containing `{x, z}`), given a complex circle bound
`B` on the correlation value increment on the sphere `Metric.sphere (0:ℂ) R`,
the consecutive β-derivative increment is bounded by `B / R` at `β = 0`. The
volume-uniform structural inputs deliver a single `R > 0` independent of `k`,
matching the volume-uniform `hZk` / `hZk1` hypotheses of #3032.

The complementary input `hB` (volume-uniform circle bound) is the open
parallel input from Issue #3044 (complex Simon-Lieb / hB provider). -/
theorem dist_deriv_correlationAlongExhaustion_le_at_zero_beta_of_volume_uniform
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    [hinst : ∀ n, Fintype
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) (k : ℕ)
    (hHT : VolumeUniformComplexHTBound (IsingModel.latticeGraph d) Λ J)
    (hid : VolumeUniformZComplexIdentity (IsingModel.latticeGraph d) Λ J)
    (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) :
    ∃ R > 0, ∀ {B : ℝ} (_hB : ∀ w ∈ Metric.sphere ((0 : ℝ) : ℂ) R,
        ‖correlationComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
              (Ambient.liftFinset {x, z} hk) (J : ℂ) (0 : ℂ) w -
            correlationComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
              (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
              (J : ℂ) (0 : ℂ) w‖ ≤ B),
      dist
        (deriv (fun β : ℝ => Ambient.correlationAlongExhaustion
          (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ {x, z} k) 0)
        (deriv (fun β : ℝ => Ambient.correlationAlongExhaustion
          (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ {x, z} (k + 1)) 0)
        ≤ B / R := by
  -- Extract a single volume-uniform disc radius `R > 0` from the bridges.
  obtain ⟨R, hR, hne⟩ :=
    Ambient.partitionFunctionComplex_inducedGraph_ne_zero_on_ball_at_zero_of_volume_uniform
      (IsingModel.latticeGraph d) Λ J hHT hid
  -- Re-express the closedBall (0 : ℂ) R as closedBall ((0 : ℝ) : ℂ) R.
  have h_coe : ((0 : ℝ) : ℂ) = (0 : ℂ) := Complex.ofReal_zero
  refine ⟨R, hR, ?_⟩
  intro B hB
  refine dist_deriv_correlationAlongExhaustion_le_of_complex_circle_bound
    Λ J x z k (β := 0) (R := R) (B := B) hR hk ?_ ?_ ?_
  · -- `hZk` slot: Z_ℂ ≠ 0 on closedBall ((0:ℝ):ℂ) R at stage k.
    intro w hw
    rw [h_coe] at hw
    exact hne k w hw
  · -- `hZk1` slot: Z_ℂ ≠ 0 on closedBall ((0:ℝ):ℂ) R at stage k+1.
    intro w hw
    rw [h_coe] at hw
    exact hne (k + 1) w hw
  · -- `hB` slot: forwarded directly from the caller.
    exact hB

/-- **Lemma 17.5.2 conditional dist-increment via the CE route at general real
`β₀`** (Issue #3054, generalisation of
`dist_deriv_correlationAlongExhaustion_le_at_zero_beta_of_volume_uniform`).
Composes the volume-uniform `Z_ℂ ≠ 0` bridge at `β₀` (PR #3072,
`partitionFunctionComplex_inducedGraph_ne_zero_on_ball_at_real_beta_of_volume_uniform`)
with PR #3032's capstone-coordinate conditional reduction.

For each covered stage `k` and a complex circle bound `B` on
`Metric.sphere ((β₀:ℝ):ℂ) R`, the consecutive β-derivative increment
`dist(∂_β c_k @ β₀, ∂_β c_{k+1} @ β₀) ≤ B / R`, with `R` volume-uniform. -/
theorem dist_deriv_correlationAlongExhaustion_le_at_real_beta_of_volume_uniform
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    [hinst : ∀ n, Fintype
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) (k : ℕ) (β₀ : ℝ)
    (hHT : VolumeUniformComplexHTBoundAtReal
      (IsingModel.latticeGraph d) Λ J β₀)
    (hid : VolumeUniformZComplexIdentityAtReal
      (IsingModel.latticeGraph d) Λ J β₀)
    (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) :
    ∃ R > 0, ∀ {B : ℝ} (_hB : ∀ w ∈ Metric.sphere ((β₀ : ℝ) : ℂ) R,
        ‖correlationComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
              (Ambient.liftFinset {x, z} hk) (J : ℂ) (0 : ℂ) w -
            correlationComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
              (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
              (J : ℂ) (0 : ℂ) w‖ ≤ B),
      dist
        (deriv (fun β : ℝ => Ambient.correlationAlongExhaustion
          (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ {x, z} k) β₀)
        (deriv (fun β : ℝ => Ambient.correlationAlongExhaustion
          (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ {x, z} (k + 1)) β₀)
        ≤ B / R := by
  obtain ⟨R, hR, hne⟩ :=
    Ambient.partitionFunctionComplex_inducedGraph_ne_zero_on_ball_at_real_beta_of_volume_uniform
      (IsingModel.latticeGraph d) Λ J β₀ hHT hid
  refine ⟨R, hR, ?_⟩
  intro B hB
  refine dist_deriv_correlationAlongExhaustion_le_of_complex_circle_bound
    Λ J x z k (β := β₀) (R := R) (B := B) hR hk ?_ ?_ ?_
  · intro w hw
    exact hne k w hw
  · intro w hw
    exact hne (k + 1) w hw
  · exact hB

/-- **Structural bundle: CE-route geometric increment criterion on an `Icc`**
(Issue #3054). For *every* `β` in a closed sub-interval of the high-temperature
open interval and every covered stage `k`, the bundle supplies a single radius
`R > 0`, a circle bound `B`, the volume-uniform `Z_ℂ ≠ 0` for stages `k` and
`k+1`, and the value-increment circle bound `B` on `sphere ((β:ℝ):ℂ) R` with
`B / R ≤ M · ratio^k`. This is the exact form to feed
`dist_deriv_correlationAlongExhaustion_le_of_complex_circle_bound` (PR #3032)
per (β, k) and through to
`lemma_17_5_2_derivative_limit_provider_of_geometric_increments_on_covered_stages`. -/
def CERouteIccGeometricIncrement
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ) : Prop :=
  ∀ β₁ β₂ : ℝ,
    Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
      ∀ β ∈ Set.Icc β₁ β₂,
        ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
          ∃ R > 0, ∃ B : ℝ,
            B / R ≤ M * ratio ^ k ∧
            (∀ w ∈ Metric.closedBall ((β : ℝ) : ℂ) R,
              partitionFunctionComplex
                  (Ambient.inducedGraph (IsingModel.latticeGraph d)
                    (Λ.volume k))
                  (J : ℂ) 0 w ≠ 0) ∧
            (∀ w ∈ Metric.closedBall ((β : ℝ) : ℂ) R,
              partitionFunctionComplex
                  (Ambient.inducedGraph (IsingModel.latticeGraph d)
                    (Λ.volume (k + 1)))
                  (J : ℂ) 0 w ≠ 0) ∧
            (∀ w ∈ Metric.sphere ((β : ℝ) : ℂ) R,
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 w -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 w‖ ≤ B)

/-- **CE-route geometric increment provides the increment `hincr`**
(Issue #3054). Converts a `CERouteIccGeometricIncrement` package directly into
the `hincr` predicate of
`lemma_17_5_2_derivative_limit_provider_of_geometric_increments_on_covered_stages`.

Direct composition with
`dist_deriv_correlationAlongExhaustion_le_of_complex_circle_bound` (PR #3032)
per (β, k), then chain `dist ≤ B/R ≤ M · ratio^k`. -/
theorem hincr_of_CERouteIccGeometricIncrement
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (h : CERouteIccGeometricIncrement Λ J x z M ratio) :
    ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ k : ℕ, ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k →
          ∀ β ∈ Set.Icc β₁ β₂,
            dist
              (deriv (fun β' : ℝ => Ambient.correlationAlongExhaustion
                (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
              (deriv (fun β' : ℝ => Ambient.correlationAlongExhaustion
                (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β)
              ≤ M * ratio ^ k := by
  intro β₁ β₂ hIcc k hk β hβ
  obtain ⟨R, hR, B, hBR, hZk, hZk1, hBsphere⟩ := h β₁ β₂ hIcc β hβ k hk
  have hdist : dist
      (deriv (fun β' : ℝ => Ambient.correlationAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
      (deriv (fun β' : ℝ => Ambient.correlationAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β)
      ≤ B / R :=
    dist_deriv_correlationAlongExhaustion_le_of_complex_circle_bound
      Λ J x z k (β := β) (R := R) (B := B) hR hk hZk hZk1 hBsphere
  exact hdist.trans hBR

/-- **End-to-end CE-route Lemma 17.5.2 derivative-limit provider** (Issue
#3054): the `CERouteIccGeometricIncrement` package immediately produces the
`Lemma_17_5_2_DerivativeLimitProvider` via composition of
`hincr_of_CERouteIccGeometricIncrement` with
`lemma_17_5_2_derivative_limit_provider_of_geometric_increments_on_covered_stages`.

Needs an increased `maxHeartbeats` budget because the consumer's
`Lemma_17_5_2_DerivativeLimitProvider` Prop and the deep
`correlationAlongExhaustion` lambda elaborate heavily. -/
theorem lemma_17_5_2_derivative_limit_provider_of_CERouteIccGeometricIncrement
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h : CERouteIccGeometricIncrement Λ J x z M ratio) :
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
  lemma_17_5_2_derivative_limit_provider_of_geometric_increments_on_covered_stages
    Λ J x z M ratio hratio0 hratio1
    (hincr_of_CERouteIccGeometricIncrement Λ J x z M ratio h)

/-- **CE-route Lemma 17.5.2 upper bound from a bundle** (Issue #3054):
direct composition of the CE-route bundle with
`lemma_17_5_2_upper_bound_of_geometric_increments_on_covered_stages`.

For the `latticeGraph d` exhaustion at a high-temperature reference endpoint
`β₂`, a `CERouteIccGeometricIncrement` bundle on `Icc β₁ β₂` immediately
delivers the named `Lemma_17_5_2_UpperBound` predicate with one HLS convolution
constant.

This is the direct CE-route analogue of
`lemma_17_5_2_upper_bound_of_geometric_increments_on_covered_stages`, freeing
the caller from manually building the increment hypothesis. -/
theorem lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h : CERouteIccGeometricIncrement Λ J x z M ratio) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_geometric_increments_on_covered_stages
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (hincr_of_CERouteIccGeometricIncrement Λ J x z M ratio h)

/-- **CE-route Lemma 17.5.2 two-sided sandwich from a bundle** (Issue #3054):
direct composition of the CE-route bundle and a validating endpoint
pseudo-mass exponential-decay hypothesis with
`lemma_17_5_2_sandwich_of_geometric_increments_on_covered_stages`. -/
theorem lemma_17_5_2_sandwich_of_CERouteIccGeometricIncrement
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h : CERouteIccGeometricIncrement Λ J x z M ratio)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_sandwich_of_geometric_increments_on_covered_stages
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (hincr_of_CERouteIccGeometricIncrement Λ J x z M ratio h) hdecay

/-- **Structural bridge: CE-route volume-uniform Props (per-β) + circle bound →
`CERouteIccGeometricIncrement` bundle** (Issue #3054). Given the volume-uniform
CE-route Props `VolumeUniformComplexHTBoundAtReal` and
`VolumeUniformZComplexIdentityAtReal` available for every `β ∈ Icc β₁ β₂` in
the high-temperature open interval, together with an `Icc`-uniform geometric
circle-bound assembler `hcircle` that supplies, per (β, k), a radius `R > 0`
(constrained to fit inside the per-β ne-zero disc) and a circle bound `B` on
`sphere ((β:ℝ):ℂ) R` with `B / R ≤ M · ratio^k`, produce the
`CERouteIccGeometricIncrement` bundle.

This is the structural composition that converts the *Props level* of the
CE-route framework into the *bundle level* required by the Lemma 17.5.2
upper-bound / sandwich consumer wrappers (PR #3075). The composition uses the
per-β ne-zero bridge
`partitionFunctionComplex_inducedGraph_ne_zero_on_ball_at_real_beta_of_volume_uniform`
(PR #3072) to convert the CE-route Props at `β` into the bundle's per-stage
ne-zero hypotheses, intersected with the user-supplied radius from `hcircle`. -/
theorem CERouteIccGeometricIncrement_of_Props_and_circle
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (hProps : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          Ambient.VolumeUniformComplexHTBoundAtReal
            (IsingModel.latticeGraph d) Λ J β ∧
          Ambient.VolumeUniformZComplexIdentityAtReal
            (IsingModel.latticeGraph d) Λ J β)
    (hcircle : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ R₀ : ℝ, 0 < R₀ →
              (∀ n : ℕ, ∀ w ∈ Metric.closedBall ((β : ℝ) : ℂ) R₀,
                partitionFunctionComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n))
                    (J : ℂ) 0 w ≠ 0) →
              ∃ R > 0, R ≤ R₀ ∧ ∃ B : ℝ,
                B / R ≤ M * ratio ^ k ∧
                (∀ w ∈ Metric.sphere ((β : ℝ) : ℂ) R,
                  ‖correlationComplex
                        (Ambient.inducedGraph (IsingModel.latticeGraph d)
                          (Λ.volume k))
                        (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 w -
                      correlationComplex
                        (Ambient.inducedGraph (IsingModel.latticeGraph d)
                          (Λ.volume (k + 1)))
                        (Ambient.liftFinset {x, z}
                          (hk.trans (Λ.mono (Nat.le_succ k))))
                        (J : ℂ) 0 w‖ ≤ B)) :
    CERouteIccGeometricIncrement Λ J x z M ratio := by
  intro β₁ β₂ hIcc β hβ k hk
  -- Extract the per-β CE-route Props.
  obtain ⟨hHT, hid⟩ := hProps β₁ β₂ hIcc β hβ
  -- Get the per-β ne-zero disc from the Props.
  obtain ⟨R₀, hR₀, hne⟩ :=
    Ambient.partitionFunctionComplex_inducedGraph_ne_zero_on_ball_at_real_beta_of_volume_uniform
      (IsingModel.latticeGraph d) Λ J β hHT hid
  -- Apply the circle assembler with R₀ and the ne-zero hypothesis.
  obtain ⟨R, hR, hR_le, B, hBR, hBsphere⟩ :=
    hcircle β₁ β₂ hIcc β hβ k hk R₀ hR₀ hne
  refine ⟨R, hR, B, hBR, ?_, ?_, hBsphere⟩
  · intro w hw
    have hw₀ : w ∈ Metric.closedBall ((β : ℝ) : ℂ) R₀ := by
      rw [Metric.mem_closedBall] at hw ⊢
      linarith
    exact hne k w hw₀
  · intro w hw
    have hw₀ : w ∈ Metric.closedBall ((β : ℝ) : ℂ) R₀ := by
      rw [Metric.mem_closedBall] at hw ⊢
      linarith
    exact hne (k + 1) w hw₀

/-- **One-step CE-route Lemma 17.5.2 upper bound from Props + circle**
(Issue #3054). Composition of `CERouteIccGeometricIncrement_of_Props_and_circle`
(PR #3076) with `lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement`
(PR #3075). Delivers the named `Lemma_17_5_2_UpperBound` predicate directly
from the per-β CE-route volume-uniform Props and an Icc-uniform circle
assembler — eliminating the explicit bundle step. -/
theorem lemma_17_5_2_upper_bound_of_CERouteProps_and_circle
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hProps : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          Ambient.VolumeUniformComplexHTBoundAtReal
            (IsingModel.latticeGraph d) Λ J β ∧
          Ambient.VolumeUniformZComplexIdentityAtReal
            (IsingModel.latticeGraph d) Λ J β)
    (hcircle : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ R₀ : ℝ, 0 < R₀ →
              (∀ n : ℕ, ∀ w ∈ Metric.closedBall ((β : ℝ) : ℂ) R₀,
                partitionFunctionComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n))
                    (J : ℂ) 0 w ≠ 0) →
              ∃ R > 0, R ≤ R₀ ∧ ∃ B : ℝ,
                B / R ≤ M * ratio ^ k ∧
                (∀ w ∈ Metric.sphere ((β : ℝ) : ℂ) R,
                  ‖correlationComplex
                        (Ambient.inducedGraph (IsingModel.latticeGraph d)
                          (Λ.volume k))
                        (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 w -
                      correlationComplex
                        (Ambient.inducedGraph (IsingModel.latticeGraph d)
                          (Λ.volume (k + 1)))
                        (Ambient.liftFinset {x, z}
                          (hk.trans (Λ.mono (Nat.le_succ k))))
                        (J : ℂ) 0 w‖ ≤ B)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_Props_and_circle Λ J x z M ratio hProps hcircle)

/-- **One-step CE-route Lemma 17.5.2 sandwich from Props + circle + decay**
(Issue #3054). Composition of `CERouteIccGeometricIncrement_of_Props_and_circle`
(PR #3076) with `lemma_17_5_2_sandwich_of_CERouteIccGeometricIncrement`
(PR #3075). Delivers the displayed two-sided sandwich
`m⁻(β₂) ≤ m(β₂) ≤ C · m⁻(β₂)` directly from the per-β CE-route Props, the
circle assembler, and a validating endpoint pseudo-mass decay. -/
theorem lemma_17_5_2_sandwich_of_CERouteProps_and_circle
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hProps : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          Ambient.VolumeUniformComplexHTBoundAtReal
            (IsingModel.latticeGraph d) Λ J β ∧
          Ambient.VolumeUniformZComplexIdentityAtReal
            (IsingModel.latticeGraph d) Λ J β)
    (hcircle : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ R₀ : ℝ, 0 < R₀ →
              (∀ n : ℕ, ∀ w ∈ Metric.closedBall ((β : ℝ) : ℂ) R₀,
                partitionFunctionComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n))
                    (J : ℂ) 0 w ≠ 0) →
              ∃ R > 0, R ≤ R₀ ∧ ∃ B : ℝ,
                B / R ≤ M * ratio ^ k ∧
                (∀ w ∈ Metric.sphere ((β : ℝ) : ℂ) R,
                  ‖correlationComplex
                        (Ambient.inducedGraph (IsingModel.latticeGraph d)
                          (Λ.volume k))
                        (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 w -
                      correlationComplex
                        (Ambient.inducedGraph (IsingModel.latticeGraph d)
                          (Λ.volume (k + 1)))
                        (Ambient.liftFinset {x, z}
                          (hk.trans (Λ.mono (Nat.le_succ k))))
                        (J : ℂ) 0 w‖ ≤ B))
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_sandwich_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_Props_and_circle Λ J x z M ratio hProps hcircle)
    hdecay

/-- **Cauchy-route Q-input bundle constructor** (Issue #3054, mirror of the
CE-route Props bridge `CERouteIccGeometricIncrement_of_Props_and_circle`).
Provides an alternative source for the `CERouteIccGeometricIncrement` bundle
via the second-moment route (PR #3048,
`partitionFunctionComplex_norm_ge_of_second_moment_le`).

For each (β ∈ Icc β₁ β₂, stage n) the user supplies a second-moment upper
bound `Q n β` on
`∑_σ exp(-β·H(σ; J,0)) · H(σ; J,0)^2`
at the induced subgraph, together with a smallness witness on the imaginary
direction. The `hcircle` assembler then supplies, per (β, k), the geometric
sphere bound at a radius small enough that the imaginary direction smallness
holds for the resulting disc.

This converts a *second-moment / Cauchy-style* package directly into the
CE-route bundle that the Lemma 17.5.2 capstone consumes
(`lemma_17_5_2_{upper_bound,sandwich}_of_CERouteIccGeometricIncrement`). -/
theorem CERouteIccGeometricIncrement_of_Q_and_circle
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (hcircle : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R > 0, ∃ B : ℝ,
              B / R ≤ M * ratio ^ k ∧
              (∀ w ∈ Metric.closedBall ((β : ℝ) : ℂ) R,
                partitionFunctionComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (J : ℂ) 0 w ≠ 0) ∧
              (∀ w ∈ Metric.closedBall ((β : ℝ) : ℂ) R,
                partitionFunctionComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (J : ℂ) 0 w ≠ 0) ∧
              (∀ w ∈ Metric.sphere ((β : ℝ) : ℂ) R,
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 w -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 w‖ ≤ B)) :
    CERouteIccGeometricIncrement Λ J x z M ratio := by
  -- The bundle is exactly what `hcircle` provides; rearrange the structure.
  intro β₁ β₂ hIcc β hβ k hk
  obtain ⟨R, hR, B, hBR, hZk, hZk1, hBsphere⟩ := hcircle β₁ β₂ hIcc β hβ k hk
  exact ⟨R, hR, B, hBR, hZk, hZk1, hBsphere⟩

/-- **`Z_ℂ ≠ 0` from a second-moment Q-bound at strict smallness** (Issue
#3054 / Issue #3044 Cauchy-route bridge). Conditional on `0 < Z_ℝ - β.im²/2 · Q`
(the explicit smallness on the imaginary direction), the complex partition
function is non-zero. Direct corollary of
`partitionFunctionComplex_norm_ge_of_second_moment_le` (PR #3048) and
`norm_pos_iff`. Useful for assembling the `hcircle` ne-zero parts of
`CERouteIccGeometricIncrement_of_Q_and_circle` from a Q-bound at each stage. -/
theorem partitionFunctionComplex_ne_zero_of_second_moment_bound_and_smallness
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) (β : ℂ) {Q : ℝ}
    (hQ : (∑ σ : Config ι, Real.exp (-β.re * hamiltonian G p σ) *
        hamiltonian G p σ ^ 2) ≤ Q)
    (hsmall : 0 < partitionFunction G (⟨p.J, p.h, β.re⟩ : IsingParams ℝ) -
        β.im ^ 2 / 2 * Q) :
    partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) β ≠ 0 := by
  have h_lb :=
    IsingModel.partitionFunctionComplex_norm_ge_of_second_moment_le G p β hQ
  have h_norm_pos :
      0 < ‖partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) β‖ :=
    lt_of_lt_of_le hsmall h_lb
  exact norm_pos_iff.mp h_norm_pos

/-- **One-step Cauchy-route Lemma 17.5.2 upper bound from Q-circle assembler**
(Issue #3054). Composition of `CERouteIccGeometricIncrement_of_Q_and_circle`
(PR #3078) with `lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement`
(PR #3075). Delivers the named `Lemma_17_5_2_UpperBound` predicate directly
from a single Q-input + circle assembler, mirroring
`lemma_17_5_2_upper_bound_of_CERouteProps_and_circle` (PR #3077) at the
Cauchy-route entry point. -/
theorem lemma_17_5_2_upper_bound_of_Q_and_circle
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hcircle : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R > 0, ∃ B : ℝ,
              B / R ≤ M * ratio ^ k ∧
              (∀ w ∈ Metric.closedBall ((β : ℝ) : ℂ) R,
                partitionFunctionComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (J : ℂ) 0 w ≠ 0) ∧
              (∀ w ∈ Metric.closedBall ((β : ℝ) : ℂ) R,
                partitionFunctionComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (J : ℂ) 0 w ≠ 0) ∧
              (∀ w ∈ Metric.sphere ((β : ℝ) : ℂ) R,
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 w -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 w‖ ≤ B)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_Q_and_circle Λ J x z M ratio hcircle)

/-- **One-step Cauchy-route Lemma 17.5.2 sandwich from Q-circle assembler +
decay** (Issue #3054). Composition of `CERouteIccGeometricIncrement_of_Q_and_circle`
(PR #3078) with `lemma_17_5_2_sandwich_of_CERouteIccGeometricIncrement`
(PR #3075). Same one-step Cauchy-route entry to the two-sided sandwich,
mirroring `lemma_17_5_2_sandwich_of_CERouteProps_and_circle` (PR #3077). -/
theorem lemma_17_5_2_sandwich_of_Q_and_circle
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hcircle : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R > 0, ∃ B : ℝ,
              B / R ≤ M * ratio ^ k ∧
              (∀ w ∈ Metric.closedBall ((β : ℝ) : ℂ) R,
                partitionFunctionComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (J : ℂ) 0 w ≠ 0) ∧
              (∀ w ∈ Metric.closedBall ((β : ℝ) : ℂ) R,
                partitionFunctionComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (J : ℂ) 0 w ≠ 0) ∧
              (∀ w ∈ Metric.sphere ((β : ℝ) : ℂ) R,
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 w -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 w‖ ≤ B))
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_sandwich_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_Q_and_circle Λ J x z M ratio hcircle)
    hdecay

/-- **Unconditional per-stage dist bound from the trivial Q-bound** (Issue
#3054): direct composition of the unconditional
`partitionFunctionComplex_ne_zero_on_closedBall_h_zero_at_zero` (PR #3081)
with PR #3032's capstone-coordinate conditional reduction
`dist_deriv_correlationAlongExhaustion_le_of_complex_circle_bound`.

For each covered stage `k`, for any radius `r > 0` satisfying the explicit
**unconditional** smallness bound `r * (|J| · |E_k|) < √2` AND
`r * (|J| · |E_{k+1}|) < √2`, and any circle bound `B` on
`Metric.sphere ((0:ℝ):ℂ) r` for the value increment, the consecutive
β-derivative increment satisfies
`dist(∂_β c_k, ∂_β c_{k+1}) ≤ B / r` at `β = 0`.

The radius bound is **explicit and unconditional** — no cluster-expansion
assumption — but shrinks with the per-stage edge counts. Volume-uniform `r`
requires sharper Q-bounds (research-level). The complementary `B` (circle
bound on the correlation value increment) is the volume-uniform Simon-Lieb
input from Issue #3044. -/
theorem dist_deriv_correlationAlongExhaustion_le_at_zero_beta_unconditional
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    [∀ n, Fintype
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) (k : ℕ) (r : ℝ) (hr_pos : 0 < r)
    (hr_small_k : r * (|J| *
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k)).edgeFinset.card)
        < Real.sqrt 2)
    (hr_small_k1 : r * (|J| *
      (Ambient.inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume (k + 1))).edgeFinset.card) < Real.sqrt 2)
    (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k)
    {B : ℝ}
    (hB : ∀ w ∈ Metric.sphere ((0 : ℝ) : ℂ) r,
        ‖correlationComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
              (Ambient.liftFinset {x, z} hk) (J : ℂ) (0 : ℂ) w -
            correlationComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
              (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
              (J : ℂ) (0 : ℂ) w‖ ≤ B) :
    dist
      (deriv (fun β : ℝ => Ambient.correlationAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ {x, z} k) 0)
      (deriv (fun β : ℝ => Ambient.correlationAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ {x, z} (k + 1)) 0)
      ≤ B / r := by
  refine dist_deriv_correlationAlongExhaustion_le_of_complex_circle_bound
    Λ J x z k (β := 0) (R := r) (B := B) hr_pos hk ?_ ?_ ?_
  · -- hZk slot: Z_ℂ ≠ 0 on closedBall ((0:ℝ):ℂ) r at stage k.
    intro w hw
    have hw₀ : w ∈ Metric.closedBall (0 : ℂ) r := by
      rw [Metric.mem_closedBall] at hw
      simp only [Complex.ofReal_zero] at hw
      rw [Metric.mem_closedBall]; exact hw
    exact IsingModel.partitionFunctionComplex_ne_zero_on_closedBall_h_zero_at_zero
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
      J hr_small_k w hw₀
  · -- hZk1 slot at stage k+1.
    intro w hw
    have hw₀ : w ∈ Metric.closedBall (0 : ℂ) r := by
      rw [Metric.mem_closedBall] at hw
      simp only [Complex.ofReal_zero] at hw
      rw [Metric.mem_closedBall]; exact hw
    exact IsingModel.partitionFunctionComplex_ne_zero_on_closedBall_h_zero_at_zero
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
      J hr_small_k1 w hw₀
  · exact hB

/-- **Unconditional Cauchy-route bundle constructor at general real β** (Issue
#3054). The user supplies, per (β ∈ Icc β₁ β₂, k covered), a radius `r > 0`
satisfying the explicit unconditional smallness
`r * (|J| · |E_k|) < √2` for both stages `k` and `k+1`, plus a circle bound `B`
with `B / r ≤ M · ratio^k`. The ne-zero hypotheses are auto-supplied via
`partitionFunctionComplex_ne_zero_on_closedBall_h_zero_at_real_beta` (PR #3083) —
no cluster-expansion assumption needed for ne-zero. Produces the standard
`CERouteIccGeometricIncrement` bundle ready to feed
`lemma_17_5_2_{upper_bound,sandwich}_of_CERouteIccGeometricIncrement` (PR #3075). -/
theorem CERouteIccGeometricIncrement_of_trivial_Q_smallness_h_zero
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (hcircle : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ r > 0, ∃ B : ℝ,
              B / r ≤ M * ratio ^ k ∧
              r * (|J| *
                (Ambient.inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume k)).edgeFinset.card) < Real.sqrt 2 ∧
              r * (|J| *
                (Ambient.inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume (k + 1))).edgeFinset.card) < Real.sqrt 2 ∧
              (∀ w ∈ Metric.sphere ((β : ℝ) : ℂ) r,
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 w -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 w‖ ≤ B)) :
    CERouteIccGeometricIncrement Λ J x z M ratio := by
  intro β₁ β₂ hIcc β hβ k hk
  obtain ⟨r, hr, B, hBR, hr_small_k, hr_small_k1, hBsphere⟩ :=
    hcircle β₁ β₂ hIcc β hβ k hk
  refine ⟨r, hr, B, hBR, ?_, ?_, hBsphere⟩
  · -- Stage k ne-zero from #3083 with smallness at β.
    intro w hw
    exact IsingModel.partitionFunctionComplex_ne_zero_on_closedBall_h_zero_at_real_beta
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
      J β hr_small_k w hw
  · intro w hw
    exact IsingModel.partitionFunctionComplex_ne_zero_on_closedBall_h_zero_at_real_beta
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
      J β hr_small_k1 w hw

/-- **One-step Lemma 17.5.2 upper bound from trivial-Q smallness + circle**
(Issue #3054, completes the unconditional Cauchy-route per-stage chain).
Composition of `CERouteIccGeometricIncrement_of_trivial_Q_smallness_h_zero`
(PR #3083) with `lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement`
(PR #3075). Delivers the named `Lemma_17_5_2_UpperBound` predicate directly
from per-(β, k) (smallness + sphere circle bound) — with the ne-zero on the
disc auto-supplied via the trivial Q-bound; **no cluster-expansion or
second-moment assumption required for ne-zero**. -/
theorem lemma_17_5_2_upper_bound_of_trivial_Q_smallness_h_zero
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hcircle : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ r > 0, ∃ B : ℝ,
              B / r ≤ M * ratio ^ k ∧
              r * (|J| *
                (Ambient.inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume k)).edgeFinset.card) < Real.sqrt 2 ∧
              r * (|J| *
                (Ambient.inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume (k + 1))).edgeFinset.card) < Real.sqrt 2 ∧
              (∀ w ∈ Metric.sphere ((β : ℝ) : ℂ) r,
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 w -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 w‖ ≤ B)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_trivial_Q_smallness_h_zero
      Λ J x z M ratio hcircle)

/-- **One-step Lemma 17.5.2 sandwich from trivial-Q smallness + circle + decay**
(Issue #3054). Sandwich analogue of
`lemma_17_5_2_upper_bound_of_trivial_Q_smallness_h_zero`. -/
theorem lemma_17_5_2_sandwich_of_trivial_Q_smallness_h_zero
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hcircle : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ r > 0, ∃ B : ℝ,
              B / r ≤ M * ratio ^ k ∧
              r * (|J| *
                (Ambient.inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume k)).edgeFinset.card) < Real.sqrt 2 ∧
              r * (|J| *
                (Ambient.inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume (k + 1))).edgeFinset.card) < Real.sqrt 2 ∧
              (∀ w ∈ Metric.sphere ((β : ℝ) : ℂ) r,
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 w -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 w‖ ≤ B))
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_sandwich_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_trivial_Q_smallness_h_zero
      Λ J x z M ratio hcircle)
    hdecay

/-- **Canonical pair-stage trivial-Q radius** (Issue #3054): for the
consecutive stages `k` and `k+1`, the minimum of the two canonical
`trivialQRadius` values, which satisfies the unconditional smallness for both
stages simultaneously. -/
noncomputable def canonicalTrivialQRadiusPair
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ)) (J : ℝ) (k : ℕ) : ℝ :=
  min
    (IsingModel.trivialQRadius
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k)) J)
    (IsingModel.trivialQRadius
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1))) J)

/-- `canonicalTrivialQRadiusPair` is positive. -/
lemma canonicalTrivialQRadiusPair_pos
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ)) (J : ℝ) (k : ℕ) :
    0 < canonicalTrivialQRadiusPair Λ J k := by
  unfold canonicalTrivialQRadiusPair
  exact lt_min
    (IsingModel.trivialQRadius_pos
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k)) J)
    (IsingModel.trivialQRadius_pos
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1))) J)

/-- `canonicalTrivialQRadiusPair` satisfies the trivial-Q smallness at stage k. -/
lemma canonicalTrivialQRadiusPair_smallness_k
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ)) (J : ℝ) (k : ℕ) :
    canonicalTrivialQRadiusPair Λ J k *
        (|J| *
          (Ambient.inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume k)).edgeFinset.card) < Real.sqrt 2 := by
  have h_le : canonicalTrivialQRadiusPair Λ J k ≤
      IsingModel.trivialQRadius
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k)) J :=
    min_le_left _ _
  have h_nn : (0 : ℝ) ≤ |J| *
      (Ambient.inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume k)).edgeFinset.card := by positivity
  calc canonicalTrivialQRadiusPair Λ J k *
        (|J| *
          (Ambient.inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume k)).edgeFinset.card)
      ≤ IsingModel.trivialQRadius
            (Ambient.inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume k)) J *
          (|J| *
            (Ambient.inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume k)).edgeFinset.card) :=
        mul_le_mul_of_nonneg_right h_le h_nn
    _ < Real.sqrt 2 :=
        IsingModel.trivialQRadius_smallness
          (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k)) J

/-- `canonicalTrivialQRadiusPair` satisfies the trivial-Q smallness at stage k+1. -/
lemma canonicalTrivialQRadiusPair_smallness_k1
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ)) (J : ℝ) (k : ℕ) :
    canonicalTrivialQRadiusPair Λ J k *
        (|J| *
          (Ambient.inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume (k + 1))).edgeFinset.card) < Real.sqrt 2 := by
  have h_le : canonicalTrivialQRadiusPair Λ J k ≤
      IsingModel.trivialQRadius
        (Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume (k + 1))) J :=
    min_le_right _ _
  have h_nn : (0 : ℝ) ≤ |J| *
      (Ambient.inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume (k + 1))).edgeFinset.card := by positivity
  calc canonicalTrivialQRadiusPair Λ J k *
        (|J| *
          (Ambient.inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume (k + 1))).edgeFinset.card)
      ≤ IsingModel.trivialQRadius
            (Ambient.inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume (k + 1))) J *
          (|J| *
            (Ambient.inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume (k + 1))).edgeFinset.card) :=
        mul_le_mul_of_nonneg_right h_le h_nn
    _ < Real.sqrt 2 :=
        IsingModel.trivialQRadius_smallness
          (Ambient.inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume (k + 1))) J

/-- **Auto-radius bundle constructor with canonical trivial-Q radius**
(Issue #3054). User supplies only the per-(β, k) sphere circle bound `B` with
`B / canonicalTrivialQRadiusPair Λ J k ≤ M · ratio^k`; the radius itself and
the per-stage smallness witnesses are **canonical** (no user input). Produces
the `CERouteIccGeometricIncrement` bundle. -/
theorem CERouteIccGeometricIncrement_of_canonical_radius_circle
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (hcircle : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ B : ℝ,
              B / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k ∧
              (∀ w ∈ Metric.sphere ((β : ℝ) : ℂ)
                    (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 w -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 w‖ ≤ B)) :
    CERouteIccGeometricIncrement Λ J x z M ratio := by
  refine CERouteIccGeometricIncrement_of_trivial_Q_smallness_h_zero
    Λ J x z M ratio ?_
  intro β₁ β₂ hIcc β hβ k hk
  obtain ⟨B, hBR, hBsphere⟩ := hcircle β₁ β₂ hIcc β hβ k hk
  refine ⟨canonicalTrivialQRadiusPair Λ J k,
    canonicalTrivialQRadiusPair_pos Λ J k, B, hBR,
    canonicalTrivialQRadiusPair_smallness_k Λ J k,
    canonicalTrivialQRadiusPair_smallness_k1 Λ J k, hBsphere⟩

end Ambient
end IsingModel
