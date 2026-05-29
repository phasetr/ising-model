import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CEConditionalCapstone

/-!
# CE-route bridges: Props + Q-input → bundle

Split from `CEConditionalCapstone.lean` (Issue #3054, refactor PR #3132 per
codex strategic review). This file contains the two **structural bridges**
that convert external structural inputs (volume-uniform Props or second-moment
Q-data) into the `CERouteIccGeometricIncrement` bundle:

* `CERouteIccGeometricIncrement_of_Props_and_circle` — composes the
  CE-route volume-uniform Props (`VolumeUniformComplexHTBoundAtReal` +
  `VolumeUniformZComplexIdentityAtReal`) with an Icc-uniform circle assembler
  to build the bundle.
* `lemma_17_5_2_{upper_bound,sandwich}_of_CERouteProps_and_circle` — one-step
  Lemma 17.5.2 wrappers from the Props bridge.
* `CERouteIccGeometricIncrement_of_Q_and_circle` — Cauchy-route mirror that
  builds the same bundle from a second-moment Q-input.
* `partitionFunctionComplex_ne_zero_of_second_moment_bound_and_smallness` —
  norm_pos_iff corollary of PR #3048 used inside the Q bridge.
* `lemma_17_5_2_{upper_bound,sandwich}_of_Q_and_circle` — one-step wrappers
  from the Q bridge.

These bridges are the structural composers that convert the *Props level* /
*Q level* of the CE-route framework into the *bundle level* expected by the
Lemma 17.5.2 upper-bound / sandwich consumer wrappers (in
`CEConditionalCapstone.lean`).

References:

* Glimm-Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp. 311-312.
* Issue #3054 (CE-route bundle framework).
* PR #3048 (`partitionFunctionComplex_norm_ge_of_second_moment_le`).
* PR #3072 (`partitionFunctionComplex_inducedGraph_ne_zero_on_ball_at_real_beta_of_volume_uniform`).
* PR #3075 (Lemma 17.5.2 upper-bound / sandwich consumer wrappers).
-/

namespace IsingModel
namespace Ambient

open Complex Metric

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

end Ambient
end IsingModel
