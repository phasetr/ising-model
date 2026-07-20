import IsingModel.Basic
import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Core
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.CorrelationInfinite.Basic
import IsingModel.PseudoMass.Profile
import IsingModel.PseudoMass.Lipschitz
import IsingModel.PseudoMass.FromParamsBasic.BasicSlices
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsLocalEq
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity.IccRegularity

/-!
# Regularity of concrete pseudo-mass beta profiles (4/5): interval Lipschitz estimate

Structural split (4/5) of
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity`.
This child holds the closed-interval Lipschitz estimate for `β ↦ (m⁻ β) ^ (2α + 1)` and the
GJ-aligned alias `gj_theorem_17_5_1_pseudoMass_pow_succ_lipschitz_on_Icc`.  See the
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity`
facade module for the full contents overview.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5 (pp. 311–312).
-/

namespace IsingModel

open Set

namespace Ambient

/-- **Closed-interval concrete pseudo-mass power-chain Lipschitz bound**:
pointwise differentiability of the infinite correlation profile, active-range
membership, and the HLS denominator comparison imply the interval Lipschitz
estimate for `β ↦ (m⁻ β)^(2α+1)`. -/
theorem
    pseudoMassFromParamsAtPair_beta_pow_succ_lipschitz_on_Icc_of_corr_differentiableAt
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) {β₁ β₂ K : ℝ}
    (hβ₁₂ : β₁ ≤ β₂)
    (hc_diff : ∀ β ∈ Set.Icc β₁ β₂,
      DifferentiableAt ℝ
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hcomp : ∀ β ∈ Set.Icc β₁ β₂,
      |deriv
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β| ≤
        K *
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α)) :
    |(pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) ^ (2 * α + 1) -
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β₁⟩ : IsingParams ℝ) x z) ^ (2 * α + 1)| ≤
      ↑(2 * α + 1) * K / r * (β₂ - β₁) := by
  let h : ℝ → ℝ := fun β =>
    pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z
  let c : ℝ → ℝ := fun β =>
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
  have hh_diff : ∀ β ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β) β := by
    simpa [h] using
      pseudoMassFromParamsAtPair_beta_hasDerivAt_deriv_on_Icc_of_corr_differentiableAt
        hα hr Λ J x z hc_diff hcorr
  have hc_deriv : ∀ β ∈ Set.Icc β₁ β₂, HasDerivAt c (deriv c β) β := by
    intro β hβ
    exact (hc_diff β hβ).hasDerivAt
  have hh_nonneg : ∀ β ∈ Set.Icc β₁ β₂, 0 ≤ h β := by
    intro β _hβ
    exact pseudoMassFromParamsAtPair_nonneg hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z
  have hg_eq : ∀ β ∈ Set.Icc β₁ β₂,
      (fun γ => pseudoMassG α r (h γ)) =ᶠ[nhds β] c := by
    simpa [h, c] using
      pseudoMassFromParamsAtPair_beta_pseudoMassG_eventuallyEq_on_Icc_of_corr_continuousAt
        hα hr Λ J x z
        (fun β hβ => (hc_diff β hβ).continuousAt) hcorr
  have hh_pos : ∀ β ∈ Set.Icc β₁ β₂, 0 < h β := by
    intro β hβ
    exact pseudoMassFromParamsAtPair_pos_of_corr_mem hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z (hcorr β hβ)
  have hc_pos : ∀ β ∈ Set.Icc β₁ β₂, 0 < c β := by
    intro β hβ
    exact (hcorr β hβ).1
  have hcomp' : ∀ β ∈ Set.Icc β₁ β₂,
      |deriv c β| ≤ K * c β / (h β) ^ (2 * α) := by
    intro β hβ
    simpa [h, c] using hcomp β hβ
  simpa [h, c] using
    pseudoMass_pow_succ_lipschitz α hr hβ₁₂
      hh_diff hc_deriv hh_nonneg hg_eq hh_pos hc_pos hcomp'

/-- **GJ §17.5 Theorem 17.5.1 proof outline: `m⁻(σ, A)^(2α+1)` is Lipschitz continuous in σ
A-uniformly** (GJ §17.5 pp. 311–312).

Glimm–Jaffe proves Theorem 17.5.1 ("The mass `m(σ)` in (17.5.1) is continuous as a function
of σ.") via the intermediate Lipschitz claim: `m⁻(σ, A)^(2α+1)` is Lipschitz continuous in
σ with a constant *uniform in both σ and A*. This is then combined with Lemma 17.5.2's
sandwich `0 ≤ m⁻ ≤ m ≤ const · m⁻` to conclude continuity of `m`.

This wrapper provides the Lipschitz claim under the GJ-aligned name and is a thin alias
of `pseudoMassFromParamsAtPair_beta_pow_succ_lipschitz_on_Icc_of_corr_differentiableAt`
(which gives the same claim using the concrete profile name).

The Lipschitz constant is `(2α + 1) · K / r`, where `K` is the HLS denominator comparison
coefficient (the Lebowitz IIIb factor) and `r` is the radius parameter of `pseudoMass`. The
constant is A-uniform because both `K` and `r` are.

Direct correspondence to GJ p.312:

* `dm⁻/dσ`-formula step →
  `pseudoMassFromParamsAtPair_beta_hasDerivAt_deriv_of_corr_differentiableAt`.
* Lebowitz IIIb (Cor 4.3.3) bounding the 4-point function → hypothesis `hcomp`
  `|c'| ≤ K · c / m⁻^(2α)` (caller-supplied; concrete Lebowitz application).
* Algebraic chain `m⁻^(2α) · dm⁻/dσ ≤ const` → built into the `_pow_succ_deriv_bound_*`
  helper.
* MVT integration over `[β₁, β₂]` → done inside the existing Lipschitz wrapper.

This is the **m⁻-derivative analysis section** of GJ's Theorem 17.5.1 proof in the Lean
formalization. It does NOT yet deliver Theorem 17.5.1 itself (continuity of `m`); that
requires combining with Lemma 17.5.2's sandwich and `pseudoMass` extension to `σ < σ_c`. -/
theorem gj_theorem_17_5_1_pseudoMass_pow_succ_lipschitz_on_Icc
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) {β₁ β₂ K : ℝ}
    (hβ₁₂ : β₁ ≤ β₂)
    (hc_diff : ∀ β ∈ Set.Icc β₁ β₂,
      DifferentiableAt ℝ
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hcomp : ∀ β ∈ Set.Icc β₁ β₂,
      |deriv
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β| ≤
        K *
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α)) :
    |(pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) ^ (2 * α + 1) -
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β₁⟩ : IsingParams ℝ) x z) ^ (2 * α + 1)| ≤
      ↑(2 * α + 1) * K / r * (β₂ - β₁) :=
  pseudoMassFromParamsAtPair_beta_pow_succ_lipschitz_on_Icc_of_corr_differentiableAt
    hα hr Λ J x z hβ₁₂ hc_diff hcorr hcomp

end Ambient

end IsingModel
