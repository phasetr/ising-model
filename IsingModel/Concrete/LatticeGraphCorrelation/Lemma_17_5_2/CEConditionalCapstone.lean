import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CapstoneIncrementFromComplexBound
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.IncrementCapstone
import IsingModel.AmbientComplexAnalyticity.VolumeUniformHZ
import IsingModel.ComplexAnalyticity.SecondMomentBounds
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

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

## Scope: bundle is a structural bridge, not a proof of Lemma 17.5.2

The CE-route bundles defined here (`CERouteIccGeometricIncrement`,
`CERouteIccPolyGeometricIncrement`, and the derived one-step wrappers) are
**structural bridges from a per-`(β, k)` complex circle bound to a summable
derivative increment** (consumed by `IncrementCapstone.lean`). The bundles
are abstract: each entry point accepts user-supplied data (radius `r`, sphere
bound `B`, ne-zero hypotheses, optionally `R_inc` / `C_k`) and verifies a
smallness condition — `B / r ≤ M · ratio^k` for the geometric form, or
`B / r ≤ M · (2k+3)^d · ratio^k` for the poly-geometric form. The data
themselves must come from elsewhere.

**Current limitation of the Cauchy-derived data:** If the per-stage Lipschitz
constants `C_k`, `C_{k+1}` are supplied via `correlationComplex_lipschitz_on_closedBall`
(PR #3124) using the Cauchy estimate `correlationComplex_norm_deriv_le_of_norm_le_on_sphere`
(#3052), the resulting `C_k` are **bounded below by `M_real / z_min / R_cauchy`**.
For the unconditional per-fixed-volume route at `h = 0` (trivial-Q smallness),
the available disc radius `r = canonicalTrivialQRadiusPair Λ J k = O(1/|Λ_k|)`
shrinks with the volume, and so does any Cauchy radius `R_cauchy ≤ r`, giving
`C_k → ∞` rather than `0`. After the triangle decomposition
`B ≤ R_inc + (C_k + C_{k+1}) · r` from `sphere_circle_bound_of_real_inc_and_lipschitz`,
the smallness reduces to `R_inc / r + (C_k + C_{k+1}) ≤ M · ratio^k → 0`,
which the non-decaying `(C_k + C_{k+1})` term cannot satisfy. **No code in this
file is mathematically unsatisfiable** — the bundles accept any abstract
`(R_inc, C_k)`; the limitation is in the available *concrete* data, not the
abstract interface.

**Where the bundles DO close Lemma 17.5.2:**

When the user can supply either of:

* **Volume-uniform disc radius** `r` (constant in `k`) together with
  volume-uniform `Z_ℂ ≠ 0` on that disc — requires complex
  cluster-expansion convergence (research-level open input, Issue #3054).
  With constant `r`, the Cauchy Lipschitz at radius `r` is volume-uniform
  but still constant; combined with a volume-uniform geometric-decay circle
  bound `B` (Issue #3044, complex Simon-Lieb), the smallness closes.

* **Decaying abstract Lipschitz** `C_k → 0` (not from the simple Cauchy
  estimate; e.g., from a finer complex analysis input). The bundle is
  agnostic about how `C_k` is produced.

For users with a **direct increment bound** (`dist(∂_β c_k, ∂_β c_{k+1}) ≤
M · ratio^k` already in hand from any other route), see
`lemma_17_5_2_{upper_bound,capstone}_of_{geometric,poly_geometric}_increments_on_covered_stages`
in `IncrementCapstone.lean` — these take `hincr` directly and bypass the
CE-route bundle entirely. The CE-route here is the natural assembly when
`hincr` is to be derived from complex analyticity + Cauchy estimate, but it
is not the only assembly.
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

/-- **One-step Lemma 17.5.2 upper bound from canonical-radius circle bound**
(Issue #3054). Composition of `CERouteIccGeometricIncrement_of_canonical_radius_circle`
(PR #3086) with `lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement`
(PR #3075). Delivers `Lemma_17_5_2_UpperBound` directly from a single
per-(β, k) sphere circle bound at the canonical pair-stage radius — no
smallness witness, no ne-zero hypothesis required. -/
theorem lemma_17_5_2_upper_bound_of_canonical_radius_circle
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
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_canonical_radius_circle Λ J x z M ratio hcircle)

/-- **One-step Lemma 17.5.2 sandwich from canonical-radius circle bound + decay**
(Issue #3054). Sandwich analogue of `lemma_17_5_2_upper_bound_of_canonical_radius_circle`. -/
theorem lemma_17_5_2_sandwich_of_canonical_radius_circle
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
    (CERouteIccGeometricIncrement_of_canonical_radius_circle Λ J x z M ratio hcircle)
    hdecay

/-- **Sphere circle bound via direct triangle inequality with per-stage
Lipschitz and real-axis values** (Issue #3054). For each `w` on
`Metric.sphere ((β₀:ℝ):ℂ) r`, the cross-stage value increment satisfies:
`‖corr_ℂ G_k(w) - corr_ℂ G_{k+1}(w)‖ ≤ R_inc + (C_k + C_k1) · r`.

Proof: direct triangle inequality
`‖a - d‖ ≤ ‖a - b‖ + ‖b - c‖ + ‖c - d‖`
where `a := corr_ℂ G_k(w)`, `b := corr_ℂ G_k(w.re)`,
`c := corr_ℂ G_{k+1}(w.re)`, `d := corr_ℂ G_{k+1}(w)`. Per-stage Lipschitz
hypotheses bound `‖a - b‖` and `‖c - d‖`; the real-axis identity
`corr_ℂ G((w.re:ℝ):ℂ) = (correlation G ⟨J,0,w.re⟩ : ℂ)` makes `b - c` a cast
of a real difference, with `‖b - c‖` equal to the absolute value of the real
increment; sphere geometry gives `‖w - w.re‖ ≤ r`. Bypasses vertex-type
incompatibility that prevents direct use of
`correlationComplex_diff_norm_le_real_diff_plus_lipschitz` (#3050). -/
theorem sphere_circle_bound_of_real_inc_and_lipschitz
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (k : ℕ)
    (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k)
    (β₀ r R_inc C_k C_k1 : ℝ)
    (h_real_inc : ∀ β_re : ℝ, β_re ∈ Set.Icc (β₀ - r) (β₀ + r) →
      |correlation
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
            (⟨J, 0, β_re⟩ : IsingParams ℝ)
            (Ambient.liftFinset {x, z} hk) -
          correlation
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
            (⟨J, 0, β_re⟩ : IsingParams ℝ)
            (Ambient.liftFinset {x, z}
              (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc)
    (h_lip_k : ∀ β ∈ Metric.sphere ((β₀ : ℝ) : ℂ) r,
      ‖correlationComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
            (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 β -
          correlationComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
            (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((β.re : ℝ) : ℂ)‖
        ≤ C_k * ‖β - ((β.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β ∈ Metric.sphere ((β₀ : ℝ) : ℂ) r,
      ‖correlationComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
            (Ambient.liftFinset {x, z}
              (hk.trans (Λ.mono (Nat.le_succ k)))) (J : ℂ) 0 β -
          correlationComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
            (Ambient.liftFinset {x, z}
              (hk.trans (Λ.mono (Nat.le_succ k)))) (J : ℂ) 0 ((β.re : ℝ) : ℂ)‖
        ≤ C_k1 * ‖β - ((β.re : ℝ) : ℂ)‖)
    (hC_k_nn : 0 ≤ C_k) (hC_k1_nn : 0 ≤ C_k1) :
    ∀ w ∈ Metric.sphere ((β₀ : ℝ) : ℂ) r,
      ‖correlationComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
            (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 w -
          correlationComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
            (Ambient.liftFinset {x, z}
              (hk.trans (Λ.mono (Nat.le_succ k))))
            (J : ℂ) 0 w‖ ≤ R_inc + (C_k + C_k1) * r := by
  intro w hw
  have hb_aux := IsingModel.correlation_ofReal_eq_correlationComplex
    (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
    (⟨J, 0, w.re⟩ : IsingParams ℝ) (Ambient.liftFinset {x, z} hk)
  simp only [Complex.ofReal_zero] at hb_aux
  have hb_real : correlationComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((w.re : ℝ) : ℂ) =
      ((correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
        (⟨J, 0, w.re⟩ : IsingParams ℝ)
        (Ambient.liftFinset {x, z} hk) : ℝ) : ℂ) := hb_aux.symm
  have hc_aux := IsingModel.correlation_ofReal_eq_correlationComplex
    (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
    (⟨J, 0, w.re⟩ : IsingParams ℝ)
    (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
  simp only [Complex.ofReal_zero] at hc_aux
  have hc_real : correlationComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
      (Ambient.liftFinset {x, z}
        (hk.trans (Λ.mono (Nat.le_succ k)))) (J : ℂ) 0 ((w.re : ℝ) : ℂ) =
      ((correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
        (⟨J, 0, w.re⟩ : IsingParams ℝ)
        (Ambient.liftFinset {x, z}
          (hk.trans (Λ.mono (Nat.le_succ k)))) : ℝ) : ℂ) := hc_aux.symm
  rw [Metric.mem_sphere] at hw
  have h_w_β₀_norm_eq : ‖w - ((β₀ : ℝ) : ℂ)‖ = r := by
    rw [← Complex.dist_eq]; exact hw
  have h_w_wre_norm_le_r : ‖w - ((w.re : ℝ) : ℂ)‖ ≤ r := by
    have h_im_abs : |w.im| ≤ ‖w - ((β₀ : ℝ) : ℂ)‖ := by
      have h_sub_im : (w - ((β₀ : ℝ) : ℂ)).im = w.im := by simp
      have := Complex.abs_im_le_norm (w - ((β₀ : ℝ) : ℂ))
      rw [h_sub_im] at this; exact this
    have h_im_abs_eq : ‖w - ((w.re : ℝ) : ℂ)‖ = |w.im| := by
      have h_sub_w_wre : w - ((w.re : ℝ) : ℂ) = w.im • Complex.I :=
        Complex.ext (by simp) (by simp)
      rw [h_sub_w_wre]; simp
    linarith [h_im_abs_eq, h_im_abs, h_w_β₀_norm_eq]
  have h_re_abs : |w.re - β₀| ≤ r := by
    have h_re_sub : (w - ((β₀ : ℝ) : ℂ)).re = w.re - β₀ := by simp
    have := Complex.abs_re_le_norm (w - ((β₀ : ℝ) : ℂ))
    rw [h_re_sub] at this; linarith
  have h_real_mem : w.re ∈ Set.Icc (β₀ - r) (β₀ + r) := by
    refine ⟨?_, ?_⟩
    · linarith [abs_le.mp h_re_abs |>.1]
    · linarith [abs_le.mp h_re_abs |>.2]
  have h_ab := h_lip_k w hw
  have h_dc_norm := h_lip_k1 w hw
  have h_cd : ‖correlationComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
        (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
        (J : ℂ) 0 ((w.re : ℝ) : ℂ) -
      correlationComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
        (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
        (J : ℂ) 0 w‖ ≤ C_k1 * ‖w - ((w.re : ℝ) : ℂ)‖ := by
    have h_neg : (correlationComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
        (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
        (J : ℂ) 0 ((w.re : ℝ) : ℂ) -
      correlationComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
        (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
        (J : ℂ) 0 w) = -(correlationComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
        (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
        (J : ℂ) 0 w -
      correlationComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
        (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
        (J : ℂ) 0 ((w.re : ℝ) : ℂ)) := by ring
    rw [h_neg, norm_neg]
    exact h_dc_norm
  have h_real_bound := h_real_inc w.re h_real_mem
  set a := correlationComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 w
  set b := correlationComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((w.re : ℝ) : ℂ)
  set c := correlationComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
      (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
      (J : ℂ) 0 ((w.re : ℝ) : ℂ)
  set d_ := correlationComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
      (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
      (J : ℂ) 0 w
  have h_tri : ‖a - d_‖ ≤ ‖a - b‖ + ‖b - c‖ + ‖c - d_‖ := by
    have h_decomp : a - d_ = (a - b) + ((b - c) + (c - d_)) := by ring
    rw [h_decomp]
    have h1 := norm_add_le (a - b) ((b - c) + (c - d_))
    have h2 := norm_add_le (b - c) (c - d_)
    linarith
  have h_bc_eq : ‖b - c‖ = |correlation
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
      (⟨J, 0, w.re⟩ : IsingParams ℝ)
      (Ambient.liftFinset {x, z} hk) -
      correlation
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
      (⟨J, 0, w.re⟩ : IsingParams ℝ)
      (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))| := by
    rw [show b - c = (((correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
        (⟨J, 0, w.re⟩ : IsingParams ℝ)
        (Ambient.liftFinset {x, z} hk) -
      correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
        (⟨J, 0, w.re⟩ : IsingParams ℝ)
        (Ambient.liftFinset {x, z}
          (hk.trans (Λ.mono (Nat.le_succ k))))) : ℝ) : ℂ) from by
      rw [hb_real, hc_real]; push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [h_bc_eq] at h_tri
  have h_ab_le_r : ‖a - b‖ ≤ C_k * r :=
    le_trans h_ab (mul_le_mul_of_nonneg_left h_w_wre_norm_le_r hC_k_nn)
  have h_cd_le_r : ‖c - d_‖ ≤ C_k1 * r :=
    le_trans h_cd (mul_le_mul_of_nonneg_left h_w_wre_norm_le_r hC_k1_nn)
  nlinarith [h_tri, h_real_bound, h_ab_le_r, h_cd_le_r]

/-- **Canonical-radius bundle from real-axis value increment + Lipschitz**
(Issue #3054). Composes `sphere_circle_bound_of_real_inc_and_lipschitz`
(PR #3089) with `CERouteIccGeometricIncrement_of_canonical_radius_circle`
(PR #3086). User supplies, per (β ∈ Icc, k covered), `(R_inc, C_k, C_k1)`
satisfying
`(R_inc + (C_k + C_k1) · canonicalTrivialQRadiusPair) / canonicalTrivialQRadiusPair ≤ M · ratio^k`,
the real-axis value increment bound `R_inc` on `[β - r, β + r]`, and per-stage
Lipschitz hypotheses. Produces the bundle directly — **no smallness witness,
no ne-zero hypothesis, no sphere circle bound**; just the Cauchy-route
mathematical inputs. -/
theorem CERouteIccGeometricIncrement_of_canonical_radius_R_inc_lipschitz
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (h_inputs : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C_k C_k1 : ℝ,
              0 ≤ C_k ∧ 0 ≤ C_k1 ∧
              (R_inc + (C_k + C_k1) * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k1 * ‖b - ((b.re : ℝ) : ℂ)‖)) :
    CERouteIccGeometricIncrement Λ J x z M ratio := by
  refine CERouteIccGeometricIncrement_of_canonical_radius_circle
    Λ J x z M ratio ?_
  intro β₁ β₂ hIcc β hβ k hk
  obtain ⟨R_inc, C_k, C_k1, hC_k_nn, hC_k1_nn, hBR, h_real_inc, h_lip_k, h_lip_k1⟩ :=
    h_inputs β₁ β₂ hIcc β hβ k hk
  refine ⟨R_inc + (C_k + C_k1) * canonicalTrivialQRadiusPair Λ J k, hBR, ?_⟩
  exact sphere_circle_bound_of_real_inc_and_lipschitz Λ J x z k hk
    β (canonicalTrivialQRadiusPair Λ J k) R_inc C_k C_k1
    h_real_inc h_lip_k h_lip_k1 hC_k_nn hC_k1_nn

/-- **One-step Lemma 17.5.2 upper bound from R_inc + Lipschitz** (Issue #3054).
Composition of `CERouteIccGeometricIncrement_of_canonical_radius_R_inc_lipschitz`
(PR #3090) with `lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement`
(PR #3075). Delivers `Lemma_17_5_2_UpperBound` directly from per-(β, k)
Cauchy-route mathematical inputs (R_inc + per-stage Lipschitz). -/
theorem lemma_17_5_2_upper_bound_of_R_inc_lipschitz
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h_inputs : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C_k C_k1 : ℝ,
              0 ≤ C_k ∧ 0 ≤ C_k1 ∧
              (R_inc + (C_k + C_k1) * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k1 * ‖b - ((b.re : ℝ) : ℂ)‖)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_canonical_radius_R_inc_lipschitz
      Λ J x z M ratio h_inputs)

/-- **One-step Lemma 17.5.2 sandwich from R_inc + Lipschitz + decay**
(Issue #3054). Sandwich analogue. -/
theorem lemma_17_5_2_sandwich_of_R_inc_lipschitz
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h_inputs : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C_k C_k1 : ℝ,
              0 ≤ C_k ∧ 0 ≤ C_k1 ∧
              (R_inc + (C_k + C_k1) * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k1 * ‖b - ((b.re : ℝ) : ℂ)‖))
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
    (CERouteIccGeometricIncrement_of_canonical_radius_R_inc_lipschitz
      Λ J x z M ratio h_inputs)
    hdecay

/-- **Uniform-C bundle constructor: single Lipschitz for both stages** (Issue
#3054). Convenience specialisation of
`CERouteIccGeometricIncrement_of_canonical_radius_R_inc_lipschitz` (PR #3090)
where a single `C ≥ 0` bounds both stages' Lipschitz. User supplies
`(R_inc, C)` (instead of `(R_inc, C_k, C_k1)`) with
`(R_inc + 2·C·canonicalTrivialQRadiusPair) / canonicalTrivialQRadiusPair ≤ M·ratio^k`. -/
theorem CERouteIccGeometricIncrement_of_canonical_radius_R_inc_uniform_C
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (h_inputs : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C : ℝ,
              0 ≤ C ∧
              (R_inc + 2 * C * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)) :
    CERouteIccGeometricIncrement Λ J x z M ratio := by
  refine CERouteIccGeometricIncrement_of_canonical_radius_R_inc_lipschitz
    Λ J x z M ratio ?_
  intro β₁ β₂ hIcc β hβ k hk
  obtain ⟨R_inc, C, hC_nn, hBR, h_real_inc, h_lip_k, h_lip_k1⟩ :=
    h_inputs β₁ β₂ hIcc β hβ k hk
  refine ⟨R_inc, C, C, hC_nn, hC_nn, ?_, h_real_inc, h_lip_k, h_lip_k1⟩
  have hsimp : C + C = 2 * C := by ring
  rw [hsimp]
  exact hBR

/-- **One-step Lemma 17.5.2 upper bound from R_inc + uniform-C** (Issue #3054).
Composition of `CERouteIccGeometricIncrement_of_canonical_radius_R_inc_uniform_C`
(PR #3092) with `lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement`
(PR #3075). Delivers `Lemma_17_5_2_UpperBound` directly from per-(β, k) inputs
`(R_inc, C)` with a single Lipschitz `C` covering both stages. -/
theorem lemma_17_5_2_upper_bound_of_R_inc_uniform_C
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h_inputs : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C : ℝ,
              0 ≤ C ∧
              (R_inc + 2 * C * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_canonical_radius_R_inc_uniform_C
      Λ J x z M ratio h_inputs)

/-- **One-step Lemma 17.5.2 sandwich from R_inc + uniform-C + decay** (Issue #3054). -/
theorem lemma_17_5_2_sandwich_of_R_inc_uniform_C
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h_inputs : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C : ℝ,
              0 ≤ C ∧
              (R_inc + 2 * C * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖))
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
    (CERouteIccGeometricIncrement_of_canonical_radius_R_inc_uniform_C
      Λ J x z M ratio h_inputs)
    hdecay

/-- **Explicit `latticeGraph` lower bound for `trivialQRadius`** (Issue #3054).
For the induced lattice graph `inducedGraph (latticeGraph d) Λ`,
`trivialQRadius G J = √2 / (|J| · |E| + 1) ≥ √2 / (|J| · d · |Λ| + 1)` via
`inducedLatticeGraph_card_edgeFinset_le` (`|E| ≤ d · |Λ|`). -/
theorem trivialQRadius_inducedLatticeGraph_lower_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) :
    Real.sqrt 2 / (|J| * (d * Fintype.card (↑Λ : Type _)) + 1) ≤
      IsingModel.trivialQRadius
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J := by
  unfold IsingModel.trivialQRadius
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_edge_le : ((Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      : ℝ) ≤ d * Fintype.card (↑Λ : Type _) :=
    inducedLatticeGraph_card_edgeFinset_le d Λ
  have hJ_abs_nn : (0 : ℝ) ≤ |J| := abs_nonneg J
  have hJE_le : |J| * ((Ambient.inducedGraph (IsingModel.latticeGraph d)
      Λ).edgeFinset.card : ℝ) ≤ |J| * (d * Fintype.card (↑Λ : Type _)) :=
    mul_le_mul_of_nonneg_left h_edge_le hJ_abs_nn
  have h_denom_le : |J| * ((Ambient.inducedGraph (IsingModel.latticeGraph d)
      Λ).edgeFinset.card : ℝ) + 1 ≤
      |J| * (d * Fintype.card (↑Λ : Type _)) + 1 := by linarith
  have h_denom_rhs_pos :
      (0 : ℝ) < |J| * ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          Λ).edgeFinset.card : ℝ) + 1 := by positivity
  exact div_le_div_of_nonneg_left hsqrt2_pos.le h_denom_rhs_pos h_denom_le

/-- **Per-stage canonical-radius lower bound from `|Λ_{k+1}|`** (Issue #3054).
`canonicalTrivialQRadiusPair Λ J k ≥ √2 / (|J| · d · |Λ.volume (k+1)| + 1)`,
using `inducedLatticeGraph_card_edgeFinset_le` and the exhaustion monotonicity
`Λ.volume k ⊆ Λ.volume (k+1)` (so `|Λ.volume k| ≤ |Λ.volume (k+1)|`). -/
theorem canonicalTrivialQRadiusPair_lower_bound_volume_succ
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ)) (J : ℝ) (k : ℕ) :
    Real.sqrt 2 / (|J| * (d * Fintype.card (↑(Λ.volume (k + 1)) : Type _)) + 1)
      ≤ canonicalTrivialQRadiusPair Λ J k := by
  unfold canonicalTrivialQRadiusPair
  have h_stage_k1_lb := trivialQRadius_inducedLatticeGraph_lower_bound d
    (Λ.volume (k + 1)) J
  have h_stage_k_lb : Real.sqrt 2 /
      (|J| * (d * Fintype.card (↑(Λ.volume (k + 1)) : Type _)) + 1) ≤
      IsingModel.trivialQRadius
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k)) J := by
    have h_mono : Λ.volume k ⊆ Λ.volume (k + 1) := Λ.mono (Nat.le_succ k)
    have h_card_le : Fintype.card (↑(Λ.volume k) : Type _) ≤
        Fintype.card (↑(Λ.volume (k + 1)) : Type _) := by
      simpa using Finset.card_le_card h_mono
    have h_card_le_R : (Fintype.card (↑(Λ.volume k) : Type _) : ℝ) ≤
        Fintype.card (↑(Λ.volume (k + 1)) : Type _) := by exact_mod_cast h_card_le
    have hJ_nn : (0 : ℝ) ≤ |J| := abs_nonneg J
    have hd_nn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have h_inner_le : (d : ℝ) * Fintype.card (↑(Λ.volume k) : Type _) ≤
        (d : ℝ) * Fintype.card (↑(Λ.volume (k + 1)) : Type _) :=
      mul_le_mul_of_nonneg_left h_card_le_R hd_nn
    have h_outer_le : |J| * ((d : ℝ) * Fintype.card (↑(Λ.volume k) : Type _)) ≤
        |J| * ((d : ℝ) * Fintype.card (↑(Λ.volume (k + 1)) : Type _)) :=
      mul_le_mul_of_nonneg_left h_inner_le hJ_nn
    have h_denom_le : |J| * ((d : ℝ) * Fintype.card (↑(Λ.volume k) : Type _)) + 1 ≤
        |J| * ((d : ℝ) * Fintype.card (↑(Λ.volume (k + 1)) : Type _)) + 1 := by
      linarith
    have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h_lhs_denom_pos : (0 : ℝ) <
        |J| * ((d : ℝ) * Fintype.card (↑(Λ.volume k) : Type _)) + 1 := by positivity
    have h_decrease : Real.sqrt 2 /
        (|J| * ((d : ℝ) * Fintype.card (↑(Λ.volume (k + 1)) : Type _)) + 1) ≤
        Real.sqrt 2 /
        (|J| * ((d : ℝ) * Fintype.card (↑(Λ.volume k) : Type _)) + 1) :=
      div_le_div_of_nonneg_left h_sqrt2_pos.le h_lhs_denom_pos h_denom_le
    exact le_trans h_decrease
      (trivialQRadius_inducedLatticeGraph_lower_bound d (Λ.volume k) J)
  exact le_min h_stage_k_lb h_stage_k1_lb

/-- **Sequence-form uniform-C bundle constructor** (Issue #3054). Convenience
specialisation of `CERouteIccGeometricIncrement_of_canonical_radius_R_inc_uniform_C`
(PR #3092) where `R_inc` and `C` are sequences `ℕ → ℝ` depending only on
the stage `k` (not on `β`). Closes the per-(β, k) existential by exhibiting
`R_inc := R_inc_seq k` and `C := C_seq k`. -/
theorem CERouteIccGeometricIncrement_of_canonical_radius_sequence
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (R_inc_seq C_seq : ℕ → ℝ)
    (hC_seq_nn : ∀ k, 0 ≤ C_seq k)
    (h_smallness : ∀ k,
      (R_inc_seq k + 2 * C_seq k * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k)
    (h_real_inc : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc_seq k)
    (h_lip_k : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖) :
    CERouteIccGeometricIncrement Λ J x z M ratio := by
  refine CERouteIccGeometricIncrement_of_canonical_radius_R_inc_uniform_C
    Λ J x z M ratio ?_
  intro β₁ β₂ hIcc β hβ k hk
  refine ⟨R_inc_seq k, C_seq k, hC_seq_nn k, h_smallness k,
    h_real_inc β₁ β₂ hIcc β hβ k hk,
    h_lip_k β₁ β₂ hIcc β hβ k hk,
    h_lip_k1 β₁ β₂ hIcc β hβ k hk⟩

/-- **One-step Lemma 17.5.2 upper bound from sequence-form (R_inc, C)** (Issue
#3054). Composition of `CERouteIccGeometricIncrement_of_canonical_radius_sequence`
(PR #3095) with `lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement`
(PR #3075). Delivers `Lemma_17_5_2_UpperBound` directly from sequences
`R_inc_seq, C_seq : ℕ → ℝ`. -/
theorem lemma_17_5_2_upper_bound_of_sequence
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (R_inc_seq C_seq : ℕ → ℝ)
    (hC_seq_nn : ∀ k, 0 ≤ C_seq k)
    (h_smallness : ∀ k,
      (R_inc_seq k + 2 * C_seq k * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k)
    (h_real_inc : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc_seq k)
    (h_lip_k : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_canonical_radius_sequence
      Λ J x z M ratio R_inc_seq C_seq hC_seq_nn h_smallness
      h_real_inc h_lip_k h_lip_k1)

/-- **One-step Lemma 17.5.2 sandwich from sequence-form + decay** (Issue #3054). -/
theorem lemma_17_5_2_sandwich_of_sequence
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (R_inc_seq C_seq : ℕ → ℝ)
    (hC_seq_nn : ∀ k, 0 ≤ C_seq k)
    (h_smallness : ∀ k,
      (R_inc_seq k + 2 * C_seq k * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k)
    (h_real_inc : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc_seq k)
    (h_lip_k : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖)
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
    (CERouteIccGeometricIncrement_of_canonical_radius_sequence
      Λ J x z M ratio R_inc_seq C_seq hC_seq_nn h_smallness
      h_real_inc h_lip_k h_lip_k1)
    hdecay

/-- **Geometric-form bundle constructor: `R_inc_k = M_R · ρ_R^k`, `C` constant**
(Issue #3054). Convenience specialisation of
`CERouteIccGeometricIncrement_of_canonical_radius_sequence` (PR #3095) where
`R_inc` is geometric and `C` is stage-independent. Matches the typical scenario
where axiom-free Simon-Lieb gives geometric real-axis decay and Cauchy estimate
gives a stage-uniform Lipschitz constant. -/
theorem CERouteIccGeometricIncrement_of_canonical_radius_geometric
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio M_R ρ_R C : ℝ)
    (hC_nn : 0 ≤ C)
    (h_smallness : ∀ k,
      (M_R * ρ_R ^ k + 2 * C * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k)
    (h_real_inc : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ M_R * ρ_R ^ k)
    (h_lip_k : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖) :
    CERouteIccGeometricIncrement Λ J x z M ratio :=
  CERouteIccGeometricIncrement_of_canonical_radius_sequence
    Λ J x z M ratio (fun k => M_R * ρ_R ^ k) (fun _ => C)
    (fun _ => hC_nn) h_smallness h_real_inc h_lip_k h_lip_k1

/-- **One-step Lemma 17.5.2 upper bound from geometric-form (M_R, ρ_R, C)**
(Issue #3054). Composition of `CERouteIccGeometricIncrement_of_canonical_radius_geometric`
(PR #3097) with `lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement`
(PR #3075). Simplest parametric form: geometric R_inc + uniform C. -/
theorem lemma_17_5_2_upper_bound_of_geometric
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio M_R ρ_R C : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hC_nn : 0 ≤ C)
    (h_smallness : ∀ k,
      (M_R * ρ_R ^ k + 2 * C * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k)
    (h_real_inc : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ M_R * ρ_R ^ k)
    (h_lip_k : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_canonical_radius_geometric
      Λ J x z M ratio M_R ρ_R C hC_nn h_smallness
      h_real_inc h_lip_k h_lip_k1)

/-- **One-step Lemma 17.5.2 sandwich from geometric-form + decay** (Issue #3054). -/
theorem lemma_17_5_2_sandwich_of_geometric
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio M_R ρ_R C : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hC_nn : 0 ≤ C)
    (h_smallness : ∀ k,
      (M_R * ρ_R ^ k + 2 * C * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k)
    (h_real_inc : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ M_R * ρ_R ^ k)
    (h_lip_k : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)
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
    (CERouteIccGeometricIncrement_of_canonical_radius_geometric
      Λ J x z M ratio M_R ρ_R C hC_nn h_smallness
      h_real_inc h_lip_k h_lip_k1)
    hdecay

/-- **Poly-geometric CE-route increment bundle** (Issue #3054). Same shape as
`CERouteIccGeometricIncrement` but with smallness
`B / r ≤ M · (2k+3)^d · ratio^k` — matching the realistic boundary-prefactor
form delivered by the cubic real-axis increment
(`correlationAlongExhaustion_cubic_succ_sub_le_poly_pow`,
`CubicShellDecaySum.lean`). Natural input to
`lemma_17_5_2_{upper_bound,capstone}_of_poly_geometric_increments_on_covered_stages`
in `IncrementCapstone.lean`. -/
def CERouteIccPolyGeometricIncrement
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ) : Prop :=
  ∀ β₁ β₂ : ℝ,
    Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
      ∀ β ∈ Set.Icc β₁ β₂,
        ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
          ∃ R > 0, ∃ B : ℝ,
            B / R ≤ M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k) ∧
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

/-- **Poly-geometric hincr conversion** (Issue #3054). Mirror of
`hincr_of_CERouteIccGeometricIncrement` for the poly·geometric form. -/
theorem hincr_of_CERouteIccPolyGeometricIncrement
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (h : CERouteIccPolyGeometricIncrement Λ J x z M ratio) :
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
              ≤ M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k) := by
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

/-- **End-to-end CE-route Lemma 17.5.2 upper bound from poly-geometric bundle**
(Issue #3054). -/
theorem lemma_17_5_2_upper_bound_of_CERouteIccPolyGeometricIncrement
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h : CERouteIccPolyGeometricIncrement Λ J x z M ratio) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_poly_geometric_increments_on_covered_stages
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (hincr_of_CERouteIccPolyGeometricIncrement Λ J x z M ratio h)

/-- **End-to-end CE-route Lemma 17.5.2 capstone from poly-geometric bundle + decay**
(Issue #3054). -/
theorem lemma_17_5_2_capstone_of_CERouteIccPolyGeometricIncrement
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h : CERouteIccPolyGeometricIncrement Λ J x z M ratio)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_poly_geometric_increments_on_covered_stages
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (hincr_of_CERouteIccPolyGeometricIncrement Λ J x z M ratio h) hdecay

/-- **Poly-geometric Q-input bundle constructor (Cauchy mirror)** (Issue
#3054). Mirror of `CERouteIccGeometricIncrement_of_Q_and_circle` (PR #3078)
for the poly·geometric form. -/
theorem CERouteIccPolyGeometricIncrement_of_Q_and_circle
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (hcircle : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R > 0, ∃ B : ℝ,
              B / R ≤ M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k) ∧
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
    CERouteIccPolyGeometricIncrement Λ J x z M ratio := by
  intro β₁ β₂ hIcc β hβ k hk
  obtain ⟨R, hR, B, hBR, hZk, hZk1, hBsphere⟩ := hcircle β₁ β₂ hIcc β hβ k hk
  exact ⟨R, hR, B, hBR, hZk, hZk1, hBsphere⟩

/-- **Poly-geometric auto-assembling Cauchy bundle** (Issue #3054). Mirror of
`CERouteIccGeometricIncrement_of_trivial_Q_smallness_h_zero` (PR #3083) for
the poly·geometric form. Auto-supplies ne-zero via trivial-Q bound. -/
theorem CERouteIccPolyGeometricIncrement_of_trivial_Q_smallness_h_zero
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (hcircle : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ r > 0, ∃ B : ℝ,
              B / r ≤ M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k) ∧
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
    CERouteIccPolyGeometricIncrement Λ J x z M ratio := by
  intro β₁ β₂ hIcc β hβ k hk
  obtain ⟨r, hr, B, hBR, hr_small_k, hr_small_k1, hBsphere⟩ :=
    hcircle β₁ β₂ hIcc β hβ k hk
  refine ⟨r, hr, B, hBR, ?_, ?_, hBsphere⟩
  · intro w hw
    exact IsingModel.partitionFunctionComplex_ne_zero_on_closedBall_h_zero_at_real_beta
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
      J β hr_small_k w hw
  · intro w hw
    exact IsingModel.partitionFunctionComplex_ne_zero_on_closedBall_h_zero_at_real_beta
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
      J β hr_small_k1 w hw

/-- **Poly-geometric canonical-radius bundle constructor** (Issue #3054). User
supplies only the sphere circle bound at the canonical pair-stage radius. -/
theorem CERouteIccPolyGeometricIncrement_of_canonical_radius_circle
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (hcircle : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ B : ℝ,
              B / canonicalTrivialQRadiusPair Λ J k ≤
                M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k) ∧
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
    CERouteIccPolyGeometricIncrement Λ J x z M ratio := by
  refine CERouteIccPolyGeometricIncrement_of_trivial_Q_smallness_h_zero
    Λ J x z M ratio ?_
  intro β₁ β₂ hIcc β hβ k hk
  obtain ⟨B, hBR, hBsphere⟩ := hcircle β₁ β₂ hIcc β hβ k hk
  refine ⟨canonicalTrivialQRadiusPair Λ J k,
    canonicalTrivialQRadiusPair_pos Λ J k, B, hBR,
    canonicalTrivialQRadiusPair_smallness_k Λ J k,
    canonicalTrivialQRadiusPair_smallness_k1 Λ J k, hBsphere⟩

/-- **Poly-geometric R_inc + Lipschitz bundle constructor** (Issue #3054).
Mirror of `CERouteIccGeometricIncrement_of_canonical_radius_R_inc_lipschitz`
for the poly·geometric prefactor form
`B / r ≤ M · (2k+3)^d · ratio^k`.

User supplies a per-(β, k) tuple `(R_inc, C_k, C_k1)` such that
* `R_inc` bounds the real-axis difference on the Icc neighbourhood of `β`
  of radius `canonicalTrivialQRadiusPair Λ J k`;
* `C_k`, `C_k1` are Lipschitz constants for the imaginary direction
  of `correlationComplex` at stages `k` and `k+1` on the canonical sphere;
* the combined estimate
  `(R_inc + (C_k + C_k1) · r) / r ≤ M · (2k+3)^d · ratio^k`
  holds where `r = canonicalTrivialQRadiusPair Λ J k`.

This automatically gives the canonical-radius sphere bound via
`sphere_circle_bound_of_real_inc_and_lipschitz` (PR #3089), and forwards
to `CERouteIccPolyGeometricIncrement_of_canonical_radius_circle`. -/
theorem CERouteIccPolyGeometricIncrement_of_canonical_radius_R_inc_lipschitz
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (h_inputs : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C_k C_k1 : ℝ,
              0 ≤ C_k ∧ 0 ≤ C_k1 ∧
              (R_inc + (C_k + C_k1) * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤
                  M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k) ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k1 * ‖b - ((b.re : ℝ) : ℂ)‖)) :
    CERouteIccPolyGeometricIncrement Λ J x z M ratio := by
  refine CERouteIccPolyGeometricIncrement_of_canonical_radius_circle
    Λ J x z M ratio ?_
  intro β₁ β₂ hIcc β hβ k hk
  obtain ⟨R_inc, C_k, C_k1, hC_k_nn, hC_k1_nn, hBR, h_real_inc, h_lip_k, h_lip_k1⟩ :=
    h_inputs β₁ β₂ hIcc β hβ k hk
  refine ⟨R_inc + (C_k + C_k1) * canonicalTrivialQRadiusPair Λ J k, hBR, ?_⟩
  exact sphere_circle_bound_of_real_inc_and_lipschitz Λ J x z k hk
    β (canonicalTrivialQRadiusPair Λ J k) R_inc C_k C_k1
    h_real_inc h_lip_k h_lip_k1 hC_k_nn hC_k1_nn

/-- **One-step Lemma 17.5.2 upper bound from R_inc + Lipschitz (poly-geometric form)**
(Issue #3054). Direct composition of
`CERouteIccPolyGeometricIncrement_of_canonical_radius_R_inc_lipschitz` (PR #3101)
with `lemma_17_5_2_upper_bound_of_CERouteIccPolyGeometricIncrement` (PR #3099):
delivers `Lemma_17_5_2_UpperBound` from per-(β, k) Cauchy-route mathematical
inputs `(R_inc, C_k, C_k1)` for the poly·geometric prefactor form
`(R_inc + (C_k+C_k1)·r) / r ≤ M·(2k+3)^d·ratio^k`. -/
theorem lemma_17_5_2_upper_bound_of_R_inc_lipschitz_poly_geometric
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h_inputs : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C_k C_k1 : ℝ,
              0 ≤ C_k ∧ 0 ≤ C_k1 ∧
              (R_inc + (C_k + C_k1) * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤
                  M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k) ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k1 * ‖b - ((b.re : ℝ) : ℂ)‖)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_CERouteIccPolyGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccPolyGeometricIncrement_of_canonical_radius_R_inc_lipschitz
      Λ J x z M ratio h_inputs)

/-- **One-step Lemma 17.5.2 capstone from R_inc + Lipschitz + decay (poly-geometric form)**
(Issue #3054). Capstone (sandwich + upper-bound predicate) analogue of
`lemma_17_5_2_upper_bound_of_R_inc_lipschitz_poly_geometric`, additionally
consuming the validating endpoint pseudo-mass exponential-decay hypothesis. -/
theorem lemma_17_5_2_capstone_of_R_inc_lipschitz_poly_geometric
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h_inputs : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C_k C_k1 : ℝ,
              0 ≤ C_k ∧ 0 ≤ C_k1 ∧
              (R_inc + (C_k + C_k1) * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤
                  M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k) ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k1 * ‖b - ((b.re : ℝ) : ℂ)‖))
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_CERouteIccPolyGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccPolyGeometricIncrement_of_canonical_radius_R_inc_lipschitz
      Λ J x z M ratio h_inputs)
    hdecay

/-- **Poly-geometric uniform-C bundle constructor** (Issue #3054). Convenience
specialisation of `CERouteIccPolyGeometricIncrement_of_canonical_radius_R_inc_lipschitz`
(PR #3101) where a single `C ≥ 0` bounds both stages' Lipschitz. User supplies
`(R_inc, C)` with `(R_inc + 2·C·r) / r ≤ M·(2k+3)^d·ratio^k`. -/
theorem CERouteIccPolyGeometricIncrement_of_canonical_radius_R_inc_uniform_C
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (h_inputs : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C : ℝ,
              0 ≤ C ∧
              (R_inc + 2 * C * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤
                  M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k) ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)) :
    CERouteIccPolyGeometricIncrement Λ J x z M ratio := by
  refine CERouteIccPolyGeometricIncrement_of_canonical_radius_R_inc_lipschitz
    Λ J x z M ratio ?_
  intro β₁ β₂ hIcc β hβ k hk
  obtain ⟨R_inc, C, hC_nn, hBR, h_real_inc, h_lip_k, h_lip_k1⟩ :=
    h_inputs β₁ β₂ hIcc β hβ k hk
  refine ⟨R_inc, C, C, hC_nn, hC_nn, ?_, h_real_inc, h_lip_k, h_lip_k1⟩
  have hsimp : C + C = 2 * C := by ring
  rw [hsimp]
  exact hBR

/-- **End-to-end Lemma 17.5.2 upper bound from R_inc + uniform-C (poly-geometric form)**
(Issue #3054). Composition with `lemma_17_5_2_upper_bound_of_CERouteIccPolyGeometricIncrement`
(PR #3099). Delivers `Lemma_17_5_2_UpperBound` directly from per-(β, k) inputs
`(R_inc, C)` for the poly·geometric prefactor form. -/
theorem lemma_17_5_2_upper_bound_of_R_inc_uniform_C_poly_geometric
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h_inputs : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C : ℝ,
              0 ≤ C ∧
              (R_inc + 2 * C * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤
                  M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k) ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_CERouteIccPolyGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccPolyGeometricIncrement_of_canonical_radius_R_inc_uniform_C
      Λ J x z M ratio h_inputs)

/-- **End-to-end Lemma 17.5.2 capstone from R_inc + uniform-C + decay (poly-geometric form)**
(Issue #3054). Capstone analogue with `hdecay`. -/
theorem lemma_17_5_2_capstone_of_R_inc_uniform_C_poly_geometric
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h_inputs : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C : ℝ,
              0 ≤ C ∧
              (R_inc + 2 * C * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤
                  M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k) ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖))
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_CERouteIccPolyGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccPolyGeometricIncrement_of_canonical_radius_R_inc_uniform_C
      Λ J x z M ratio h_inputs)
    hdecay

/-- **Poly-geometric sequence-form bundle constructor** (Issue #3054).
Convenience specialisation of `CERouteIccPolyGeometricIncrement_of_canonical_radius_R_inc_uniform_C`
(PR #3103) where `R_inc` and `C` are sequences `ℕ → ℝ` depending only on
the stage `k`. -/
theorem CERouteIccPolyGeometricIncrement_of_canonical_radius_sequence
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (R_inc_seq C_seq : ℕ → ℝ)
    (hC_seq_nn : ∀ k, 0 ≤ C_seq k)
    (h_smallness : ∀ k,
      (R_inc_seq k + 2 * C_seq k * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤
          M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k))
    (h_real_inc : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc_seq k)
    (h_lip_k : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖) :
    CERouteIccPolyGeometricIncrement Λ J x z M ratio := by
  refine CERouteIccPolyGeometricIncrement_of_canonical_radius_R_inc_uniform_C
    Λ J x z M ratio ?_
  intro β₁ β₂ hIcc β hβ k hk
  refine ⟨R_inc_seq k, C_seq k, hC_seq_nn k, h_smallness k,
    h_real_inc β₁ β₂ hIcc β hβ k hk,
    h_lip_k β₁ β₂ hIcc β hβ k hk,
    h_lip_k1 β₁ β₂ hIcc β hβ k hk⟩

/-- **End-to-end Lemma 17.5.2 upper bound from sequence-form (poly-geometric)**
(Issue #3054). -/
theorem lemma_17_5_2_upper_bound_of_sequence_poly_geometric
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (R_inc_seq C_seq : ℕ → ℝ)
    (hC_seq_nn : ∀ k, 0 ≤ C_seq k)
    (h_smallness : ∀ k,
      (R_inc_seq k + 2 * C_seq k * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤
          M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k))
    (h_real_inc : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc_seq k)
    (h_lip_k : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_CERouteIccPolyGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccPolyGeometricIncrement_of_canonical_radius_sequence
      Λ J x z M ratio R_inc_seq C_seq hC_seq_nn h_smallness
      h_real_inc h_lip_k h_lip_k1)

/-- **End-to-end Lemma 17.5.2 capstone from sequence-form + decay (poly-geometric)**
(Issue #3054). -/
theorem lemma_17_5_2_capstone_of_sequence_poly_geometric
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (R_inc_seq C_seq : ℕ → ℝ)
    (hC_seq_nn : ∀ k, 0 ≤ C_seq k)
    (h_smallness : ∀ k,
      (R_inc_seq k + 2 * C_seq k * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤
          M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k))
    (h_real_inc : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc_seq k)
    (h_lip_k : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_CERouteIccPolyGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccPolyGeometricIncrement_of_canonical_radius_sequence
      Λ J x z M ratio R_inc_seq C_seq hC_seq_nn h_smallness
      h_real_inc h_lip_k h_lip_k1)
    hdecay

/-- **Poly-geometric geometric-form bundle constructor: `R_inc_k = M_R · ρ_R^k`,
`C` constant** (Issue #3054). Convenience specialisation of
`CERouteIccPolyGeometricIncrement_of_canonical_radius_sequence` (PR #3104)
where `R_inc` is geometric and `C` is stage-independent. -/
theorem CERouteIccPolyGeometricIncrement_of_canonical_radius_geometric
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio M_R ρ_R C : ℝ)
    (hC_nn : 0 ≤ C)
    (h_smallness : ∀ k,
      (M_R * ρ_R ^ k + 2 * C * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤
          M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k))
    (h_real_inc : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ M_R * ρ_R ^ k)
    (h_lip_k : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖) :
    CERouteIccPolyGeometricIncrement Λ J x z M ratio :=
  CERouteIccPolyGeometricIncrement_of_canonical_radius_sequence
    Λ J x z M ratio (fun k => M_R * ρ_R ^ k) (fun _ => C)
    (fun _ => hC_nn) h_smallness h_real_inc h_lip_k h_lip_k1

/-- **End-to-end Lemma 17.5.2 upper bound from geometric-form (poly-geometric)**
(Issue #3054). Simplest parametric form for the poly-geometric prefactor:
geometric R_inc + uniform C. -/
theorem lemma_17_5_2_upper_bound_of_geometric_poly_geometric
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio M_R ρ_R C : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hC_nn : 0 ≤ C)
    (h_smallness : ∀ k,
      (M_R * ρ_R ^ k + 2 * C * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤
          M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k))
    (h_real_inc : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ M_R * ρ_R ^ k)
    (h_lip_k : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_CERouteIccPolyGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccPolyGeometricIncrement_of_canonical_radius_geometric
      Λ J x z M ratio M_R ρ_R C hC_nn h_smallness
      h_real_inc h_lip_k h_lip_k1)

/-- **End-to-end Lemma 17.5.2 capstone from geometric-form + decay (poly-geometric)**
(Issue #3054). -/
theorem lemma_17_5_2_capstone_of_geometric_poly_geometric
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio M_R ρ_R C : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hC_nn : 0 ≤ C)
    (h_smallness : ∀ k,
      (M_R * ρ_R ^ k + 2 * C * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤
          M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k))
    (h_real_inc : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ M_R * ρ_R ^ k)
    (h_lip_k : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_CERouteIccPolyGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccPolyGeometricIncrement_of_canonical_radius_geometric
      Λ J x z M ratio M_R ρ_R C hC_nn h_smallness
      h_real_inc h_lip_k h_lip_k1)
    hdecay

/-- **Fully-concrete CE-route capstone (geometric form): replaces `hdecay` by
`pseudoMass ≤ -log(β₂J·2d)`** (Issue #3054). Composes
`CERouteIccGeometricIncrement` bundle with the fully-concrete
`lemma_17_5_2_capstone_of_geometric_increments_on_covered_stages_and_pseudoMass_le_rate`
(Issue #2931); both sides of the Lemma 17.5.2 sandwich are driven by concrete
scalar inputs (geometric increment decay and pseudo-mass high-temperature rate
bound). -/
theorem lemma_17_5_2_capstone_of_CERouteIccGeometricIncrement_and_pseudoMass_le_rate
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h : CERouteIccGeometricIncrement Λ J x z M ratio)
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z ≤
        -Real.log (β₂ * J * ↑(2 * d))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_geometric_increments_on_covered_stages_and_pseudoMass_le_rate
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (hincr_of_CERouteIccGeometricIncrement Λ J x z M ratio h) hle

/-- **Fully-concrete CE-route capstone (poly-geometric form): replaces `hdecay`
by `pseudoMass ≤ -log(β₂J·2d)`** (Issue #3054). Poly-geometric analogue of
the previous lemma, composing the `CERouteIccPolyGeometricIncrement` bundle
with `lemma_17_5_2_capstone_of_poly_geometric_increments_on_covered_stages_and_pseudoMass_le_rate`
(Issue #2931). -/
theorem lemma_17_5_2_capstone_of_CERouteIccPolyGeometricIncrement_and_pseudoMass_le_rate
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h : CERouteIccPolyGeometricIncrement Λ J x z M ratio)
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z ≤
        -Real.log (β₂ * J * ↑(2 * d))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_poly_geometric_increments_on_covered_stages_and_pseudoMass_le_rate
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (hincr_of_CERouteIccPolyGeometricIncrement Λ J x z M ratio h) hle

/-- **One-step Lemma 17.5.2 fully-concrete capstone from geometric-form (M_R, ρ_R, C)
+ pseudoMass ≤ rate** (Issue #3054). Composes
`CERouteIccGeometricIncrement_of_canonical_radius_geometric` (PR #3097) with
the fully-concrete CE-route capstone (PR #3106) — both sides of the Lemma 17.5.2
sandwich are driven by concrete scalar inputs `(M_R, ρ_R, C)` plus `hle`. -/
theorem lemma_17_5_2_capstone_of_geometric_and_pseudoMass_le_rate
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio M_R ρ_R C : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hC_nn : 0 ≤ C)
    (h_smallness : ∀ k,
      (M_R * ρ_R ^ k + 2 * C * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k)
    (h_real_inc : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ M_R * ρ_R ^ k)
    (h_lip_k : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z ≤
        -Real.log (β₂ * J * ↑(2 * d))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_CERouteIccGeometricIncrement_and_pseudoMass_le_rate
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_canonical_radius_geometric
      Λ J x z M ratio M_R ρ_R C hC_nn h_smallness
      h_real_inc h_lip_k h_lip_k1)
    hle

/-- **One-step Lemma 17.5.2 fully-concrete capstone from geometric-form
(poly-geometric) + pseudoMass ≤ rate** (Issue #3054). Composes
`CERouteIccPolyGeometricIncrement_of_canonical_radius_geometric` (PR #3105)
with the fully-concrete poly-geometric CE-route capstone (PR #3106). -/
theorem lemma_17_5_2_capstone_of_geometric_poly_geometric_and_pseudoMass_le_rate
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio M_R ρ_R C : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hC_nn : 0 ≤ C)
    (h_smallness : ∀ k,
      (M_R * ρ_R ^ k + 2 * C * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤
          M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k))
    (h_real_inc : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ M_R * ρ_R ^ k)
    (h_lip_k : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z ≤
        -Real.log (β₂ * J * ↑(2 * d))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_CERouteIccPolyGeometricIncrement_and_pseudoMass_le_rate
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccPolyGeometricIncrement_of_canonical_radius_geometric
      Λ J x z M ratio M_R ρ_R C hC_nn h_smallness
      h_real_inc h_lip_k h_lip_k1)
    hle

/-- **One-step Lemma 17.5.2 fully-concrete capstone from sequence-form (geometric)
+ pseudoMass ≤ rate** (Issue #3054). -/
theorem lemma_17_5_2_capstone_of_sequence_and_pseudoMass_le_rate
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (R_inc_seq C_seq : ℕ → ℝ)
    (hC_seq_nn : ∀ k, 0 ≤ C_seq k)
    (h_smallness : ∀ k,
      (R_inc_seq k + 2 * C_seq k * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k)
    (h_real_inc : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc_seq k)
    (h_lip_k : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖)
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z ≤
        -Real.log (β₂ * J * ↑(2 * d))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_CERouteIccGeometricIncrement_and_pseudoMass_le_rate
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_canonical_radius_sequence
      Λ J x z M ratio R_inc_seq C_seq hC_seq_nn h_smallness
      h_real_inc h_lip_k h_lip_k1)
    hle

/-- **One-step Lemma 17.5.2 fully-concrete capstone from sequence-form
(poly-geometric) + pseudoMass ≤ rate** (Issue #3054). -/
theorem lemma_17_5_2_capstone_of_sequence_poly_geometric_and_pseudoMass_le_rate
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (R_inc_seq C_seq : ℕ → ℝ)
    (hC_seq_nn : ∀ k, 0 ≤ C_seq k)
    (h_smallness : ∀ k,
      (R_inc_seq k + 2 * C_seq k * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤
          M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k))
    (h_real_inc : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc_seq k)
    (h_lip_k : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖)
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z ≤
        -Real.log (β₂ * J * ↑(2 * d))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_CERouteIccPolyGeometricIncrement_and_pseudoMass_le_rate
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccPolyGeometricIncrement_of_canonical_radius_sequence
      Λ J x z M ratio R_inc_seq C_seq hC_seq_nn h_smallness
      h_real_inc h_lip_k h_lip_k1)
    hle

/-- **One-step Lemma 17.5.2 fully-concrete capstone from uniform-C (geometric)
+ pseudoMass ≤ rate** (Issue #3054). -/
theorem lemma_17_5_2_capstone_of_R_inc_uniform_C_and_pseudoMass_le_rate
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h_inputs : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C : ℝ,
              0 ≤ C ∧
              (R_inc + 2 * C * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖))
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z ≤
        -Real.log (β₂ * J * ↑(2 * d))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_CERouteIccGeometricIncrement_and_pseudoMass_le_rate
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_canonical_radius_R_inc_uniform_C
      Λ J x z M ratio h_inputs)
    hle

/-- **One-step Lemma 17.5.2 fully-concrete capstone from uniform-C
(poly-geometric) + pseudoMass ≤ rate** (Issue #3054). -/
theorem lemma_17_5_2_capstone_of_R_inc_uniform_C_poly_geometric_and_pseudoMass_le_rate
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h_inputs : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C : ℝ,
              0 ≤ C ∧
              (R_inc + 2 * C * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤
                  M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k) ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖))
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z ≤
        -Real.log (β₂ * J * ↑(2 * d))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_CERouteIccPolyGeometricIncrement_and_pseudoMass_le_rate
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccPolyGeometricIncrement_of_canonical_radius_R_inc_uniform_C
      Λ J x z M ratio h_inputs)
    hle

/-- **One-step Lemma 17.5.2 fully-concrete capstone from R_inc + Lipschitz
(geometric) + pseudoMass ≤ rate** (Issue #3054). -/
theorem lemma_17_5_2_capstone_of_R_inc_lipschitz_and_pseudoMass_le_rate
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h_inputs : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C_k C_k1 : ℝ,
              0 ≤ C_k ∧ 0 ≤ C_k1 ∧
              (R_inc + (C_k + C_k1) * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k1 * ‖b - ((b.re : ℝ) : ℂ)‖))
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z ≤
        -Real.log (β₂ * J * ↑(2 * d))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_CERouteIccGeometricIncrement_and_pseudoMass_le_rate
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_canonical_radius_R_inc_lipschitz
      Λ J x z M ratio h_inputs)
    hle

/-- **One-step Lemma 17.5.2 fully-concrete capstone from R_inc + Lipschitz
(poly-geometric) + pseudoMass ≤ rate** (Issue #3054). -/
theorem lemma_17_5_2_capstone_of_R_inc_lipschitz_poly_geometric_and_pseudoMass_le_rate
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h_inputs : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C_k C_k1 : ℝ,
              0 ≤ C_k ∧ 0 ≤ C_k1 ∧
              (R_inc + (C_k + C_k1) * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤
                  M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k) ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k1 * ‖b - ((b.re : ℝ) : ℂ)‖))
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z ≤
        -Real.log (β₂ * J * ↑(2 * d))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_CERouteIccPolyGeometricIncrement_and_pseudoMass_le_rate
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccPolyGeometricIncrement_of_canonical_radius_R_inc_lipschitz
      Λ J x z M ratio h_inputs)
    hle

/-- **One-step Lemma 17.5.2 fully-concrete capstone from canonical-radius circle
(geometric) + pseudoMass ≤ rate** (Issue #3054). Simplest entry: user supplies
only the per-(β, k) sphere circle bound `B` at the canonical pair-stage radius. -/
theorem lemma_17_5_2_capstone_of_canonical_radius_circle_and_pseudoMass_le_rate
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
                      (J : ℂ) 0 w‖ ≤ B))
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z ≤
        -Real.log (β₂ * J * ↑(2 * d))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_CERouteIccGeometricIncrement_and_pseudoMass_le_rate
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_canonical_radius_circle
      Λ J x z M ratio hcircle)
    hle

/-- **One-step Lemma 17.5.2 fully-concrete capstone from canonical-radius circle
(poly-geometric) + pseudoMass ≤ rate** (Issue #3054). Poly-geometric analogue:
user supplies only the per-(β, k) sphere circle bound `B`. -/
theorem lemma_17_5_2_capstone_of_canonical_radius_circle_poly_geometric_and_pseudoMass_le_rate
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
            ∃ B : ℝ,
              B / canonicalTrivialQRadiusPair Λ J k ≤
                M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k) ∧
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
                      (J : ℂ) 0 w‖ ≤ B))
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z ≤
        -Real.log (β₂ * J * ↑(2 * d))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_CERouteIccPolyGeometricIncrement_and_pseudoMass_le_rate
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccPolyGeometricIncrement_of_canonical_radius_circle
      Λ J x z M ratio hcircle)
    hle

/-- **One-step Lemma 17.5.2 fully-concrete capstone from trivial-Q smallness
+ circle (geometric) + pseudoMass ≤ rate** (Issue #3054). User supplies
per-(β, k) `(r, B, smallness witnesses, sphere bound)` + `hle`. -/
theorem lemma_17_5_2_capstone_of_trivial_Q_smallness_h_zero_and_pseudoMass_le_rate
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
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z ≤
        -Real.log (β₂ * J * ↑(2 * d))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_CERouteIccGeometricIncrement_and_pseudoMass_le_rate
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_trivial_Q_smallness_h_zero
      Λ J x z M ratio hcircle)
    hle

/-- **One-step Lemma 17.5.2 fully-concrete capstone from trivial-Q smallness
+ circle (poly-geometric) + pseudoMass ≤ rate** (Issue #3054). -/
theorem lemma_17_5_2_capstone_of_trivial_Q_smallness_h_zero_poly_geometric_and_pseudoMass_le_rate
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
              B / r ≤ M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k) ∧
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
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z ≤
        -Real.log (β₂ * J * ↑(2 * d))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_CERouteIccPolyGeometricIncrement_and_pseudoMass_le_rate
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccPolyGeometricIncrement_of_trivial_Q_smallness_h_zero
      Λ J x z M ratio hcircle)
    hle

/-- **One-step Lemma 17.5.2 fully-concrete capstone from Q-and-circle (geometric)
+ pseudoMass ≤ rate** (Issue #3054). Cauchy Q-input entry point. -/
theorem lemma_17_5_2_capstone_of_Q_and_circle_and_pseudoMass_le_rate
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
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z ≤
        -Real.log (β₂ * J * ↑(2 * d))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_CERouteIccGeometricIncrement_and_pseudoMass_le_rate
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_Q_and_circle
      Λ J x z M ratio hcircle)
    hle

/-- **One-step Lemma 17.5.2 fully-concrete capstone from Q-and-circle
(poly-geometric) + pseudoMass ≤ rate** (Issue #3054). -/
theorem lemma_17_5_2_capstone_of_Q_and_circle_poly_geometric_and_pseudoMass_le_rate
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
              B / R ≤ M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k) ∧
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
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z ≤
        -Real.log (β₂ * J * ↑(2 * d))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_CERouteIccPolyGeometricIncrement_and_pseudoMass_le_rate
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccPolyGeometricIncrement_of_Q_and_circle
      Λ J x z M ratio hcircle)
    hle

/-! ## Direct increment API (Direction 3 from codex strategic review)

The bundles defined above route the user from "complex circle bound + ne-zero
disc" to "summable derivative increment" via the Cauchy estimate. If the user
already has a direct bound on `dist(∂_β c_k, ∂_β c_{k+1})` (e.g., from a finer
complex analysis input, or from a pivot to a non-Cauchy route), they can use
the `IncrementCapstone.lean` consumers directly. The following thin pass-through
predicates make this entry point explicit and named, parallel to the CE-route
bundle interface. They do not derive the increment bound from any structural
input — they accept it directly. -/

/-- **Direct geometric-increment predicate**, parallel to
`CERouteIccGeometricIncrement` but bypassing the Cauchy decomposition entirely.
This is just a named alias for the `hincr` shape expected by
`lemma_17_5_2_{upper_bound,capstone}_of_geometric_increments_on_covered_stages`
in `IncrementCapstone.lean`. Useful as a structurally explicit entry point
when the user has a direct increment bound from any non-CE route. -/
def CERouteIccDirectGeometricIncrement
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ) : Prop :=
  ∀ β₁ β₂ : ℝ, Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
    ∀ k : ℕ, ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k →
      ∀ β ∈ Set.Icc β₁ β₂,
        dist
          (deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
          (deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β) ≤
              M * ratio ^ k

/-- **Direct poly-geometric-increment predicate**, parallel to
`CERouteIccPolyGeometricIncrement` but bypassing the Cauchy decomposition.
Named alias for the `hincr` shape expected by
`lemma_17_5_2_{upper_bound,capstone}_of_poly_geometric_increments_on_covered_stages`. -/
def CERouteIccDirectPolyGeometricIncrement
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ) : Prop :=
  ∀ β₁ β₂ : ℝ, Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
    ∀ k : ℕ, ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k →
      ∀ β ∈ Set.Icc β₁ β₂,
        dist
          (deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
          (deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β) ≤
              M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k)

/-- **End-to-end Lemma 17.5.2 upper bound from direct geometric increment**:
direct pass-through of `CERouteIccDirectGeometricIncrement` to
`lemma_17_5_2_upper_bound_of_geometric_increments_on_covered_stages`. -/
theorem lemma_17_5_2_upper_bound_of_CERouteIccDirectGeometricIncrement
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h : CERouteIccDirectGeometricIncrement Λ J x z M ratio) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_geometric_increments_on_covered_stages
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1 h

/-- **End-to-end Lemma 17.5.2 capstone from direct geometric increment + decay**:
direct pass-through of `CERouteIccDirectGeometricIncrement` and the validating
endpoint pseudo-mass exponential-decay hypothesis to
`lemma_17_5_2_capstone_of_geometric_increments_on_covered_stages`. -/
theorem lemma_17_5_2_capstone_of_CERouteIccDirectGeometricIncrement
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h : CERouteIccDirectGeometricIncrement Λ J x z M ratio)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_geometric_increments_on_covered_stages
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1 h hdecay

/-- **End-to-end Lemma 17.5.2 upper bound from direct poly-geometric increment**:
pass-through to `lemma_17_5_2_upper_bound_of_poly_geometric_increments_on_covered_stages`. -/
theorem lemma_17_5_2_upper_bound_of_CERouteIccDirectPolyGeometricIncrement
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h : CERouteIccDirectPolyGeometricIncrement Λ J x z M ratio) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_poly_geometric_increments_on_covered_stages
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1 h

/-- **End-to-end Lemma 17.5.2 capstone from direct poly-geometric increment + decay**:
pass-through to `lemma_17_5_2_capstone_of_poly_geometric_increments_on_covered_stages`. -/
theorem lemma_17_5_2_capstone_of_CERouteIccDirectPolyGeometricIncrement
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h : CERouteIccDirectPolyGeometricIncrement Λ J x z M ratio)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_capstone_of_poly_geometric_increments_on_covered_stages
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1 h hdecay

end Ambient
end IsingModel
