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


end Ambient
end IsingModel
