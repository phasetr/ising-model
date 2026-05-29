import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CEConditionalCapstone
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CEConditionalCapstonePolyGeometric

/-!
# Fully-concrete CE-route capstones via `pseudoMass ≤ -log(β₂J·2d)`

Split from `CEConditionalCapstone.lean` (Issue #3054, refactor PR #3128 per
codex strategic review). This file contains the 16 `_and_pseudoMass_le_rate`
capstone wrappers that replace the abstract `hdecay` hypothesis by the
concrete scalar condition `pseudoMass ≤ -log(β₂J·2d)`.

The wrappers compose the CE-route bundle constructors (in
`CEConditionalCapstone.lean`) with the fully-concrete
`_and_pseudoMass_le_rate` consumers from `IncrementCapstone.lean`
(Issue #2931). Both sides of the Lemma 17.5.2
sandwich are driven by concrete scalar inputs (the user-supplied bundle data
plus the pseudo-mass high-temperature rate bound `hle`).

References:

* Glimm-Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp. 311-312.
* Issue #2931 (concrete pseudo-mass route).
* Issue #3054 (CE-route bundle framework).
-/

namespace IsingModel
namespace Ambient

open Complex Metric

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

end Ambient
end IsingModel
