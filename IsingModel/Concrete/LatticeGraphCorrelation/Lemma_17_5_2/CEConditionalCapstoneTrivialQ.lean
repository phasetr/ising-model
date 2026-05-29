import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CEConditionalCapstone

/-!
# Trivial-Q smallness + canonical-radius CE-route convenience

Split from `CEConditionalCapstone.lean` (Issue #3054, refactor PR #3131 per
codex strategic review). This file contains the **unconditional trivial-Q
smallness** entry into the CE-route bundle (via
`partitionFunctionComplex_ne_zero_on_closedBall_h_zero_at_zero` from PR #3081)
and the **canonical pair-stage trivial-Q radius** auto-radius variant:

* `dist_deriv_correlationAlongExhaustion_le_at_zero_beta_unconditional` —
  direct composition of unconditional ne-zero with PR #3032's reduction.
* `CERouteIccGeometricIncrement_of_trivial_Q_smallness_h_zero` —
  auto-assembling bundle constructor from smallness + circle bound.
* `lemma_17_5_2_{upper_bound,sandwich}_of_trivial_Q_smallness_h_zero` —
  end-to-end Lemma 17.5.2 wrappers.
* `canonicalTrivialQRadiusPair` + positivity / smallness lemmas — explicit
  canonical positive radius `√2 / (|J|·|E_k|+1)` always satisfying the
  trivial-Q smallness at each stage.
* `CERouteIccGeometricIncrement_of_canonical_radius_circle` — auto-radius
  bundle constructor.
* `lemma_17_5_2_{upper_bound,sandwich}_of_canonical_radius_circle` —
  one-step wrappers.

The poly-geometric counterparts live in
`CEConditionalCapstonePolyGeometric.lean`.

References:

* Glimm-Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp. 311-312.
* Issue #3054 (CE-route bundle framework).
* PR #3081 (trivial Q-bound).
-/

namespace IsingModel
namespace Ambient

open Complex Metric

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


end Ambient
end IsingModel
