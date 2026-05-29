import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CEConditionalCapstone

/-!
# Poly-geometric CE-route bundle and convenience constructors

Split from `CEConditionalCapstone.lean` (Issue #3054, refactor PR #3129 per
codex strategic review). This file contains the **poly-geometric** form of the
CE-route bundle (smallness `B / r ≤ M · (2k+3)^d · ratio^k` matching the
realistic boundary-prefactor form from the cubic real-axis increment) and all
derived convenience constructors / one-step Lemma 17.5.2 wrappers:

* `CERouteIccPolyGeometricIncrement` — base bundle definition.
* `hincr_of_CERouteIccPolyGeometricIncrement` — conversion to the `hincr`
  shape consumed by `IncrementCapstone.lean`.
* `lemma_17_5_2_{upper_bound,capstone}_of_CERouteIccPolyGeometricIncrement` —
  end-to-end Lemma 17.5.2 wrappers.
* `CERouteIccPolyGeometricIncrement_of_*` — convenience constructors from
  Q-input / trivial-Q smallness / canonical-radius / R_inc + Lipschitz /
  uniform-C / sequence / geometric inputs.
* `lemma_17_5_2_{upper_bound,capstone}_of_*_poly_geometric` — corresponding
  one-step Lemma 17.5.2 wrappers from those convenience inputs.

The geometric form (smallness `B / r ≤ M · ratio^k`) and the
`_and_pseudoMass_le_rate` fully-concrete capstones for both forms remain in
`CEConditionalCapstone.lean` / `CEConditionalCapstonePseudoMassLeRate.lean`.

References:

* Glimm-Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp. 311-312.
* Issue #3054 (CE-route bundle framework).
* `CubicShellDecaySum.lean` (poly-geometric cubic real-axis increment).
-/

namespace IsingModel
namespace Ambient

open Complex Metric

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


end Ambient
end IsingModel
