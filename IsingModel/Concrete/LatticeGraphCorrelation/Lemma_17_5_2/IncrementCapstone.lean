import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderFiniteProfile
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderInfiniteHLS
import IsingModel.Concrete.CubicExhaustion

/-!
# GJ §17.5 Lemma 17.5.2 capstone — geometric increment upper bound

This module threads the finite-volume β-derivative increment machinery
(Issue #2931) all the way through to the named `latticeMass` upper-bound side of
Lemma 17.5.2.  It assumes a geometric decay bound on the consecutive-stage
β-derivative increments over the covered exhaustion stages, builds the
derivative-limit provider from it, and feeds the provider into the concrete
compact-ratio infinite-HLS upper-bound assembly.

The geometric increment decay is the single remaining analytic input: it is the
quantitative finite-volume convergence-rate estimate (Issue #2931, Phase 3) that
sharpens the uniform increment magnitude bound into a summable one.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider from geometric increment
decay on covered stages**: if there are `M : ℝ` and `0 ≤ ratio < 1` such that on
every closed interval inside the open high-temperature region the
consecutive-stage finite-volume β-derivative differences over the covered
exhaustion stages are bounded by `M · ratio ^ k`, then the derivative-limit
provider holds.

The geometric sequence is summable, so this is the geometric specialization of
`lemma_17_5_2_derivative_limit_provider_of_summable_increments_on_covered_stages`.
Part of Issue #2931. -/
theorem lemma_17_5_2_derivative_limit_provider_of_geometric_increments_on_covered_stages
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hincr :
      ∀ β₁ β₂ : ℝ,
        Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ k : ℕ, ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k →
            ∀ β ∈ Set.Icc β₁ β₂,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β) ≤
                M * ratio ^ k) :
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
  lemma_17_5_2_derivative_limit_provider_of_summable_increments_on_covered_stages
    Λ J x z (fun k => M * ratio ^ k)
    ((summable_geometric_of_lt_one hratio0 hratio1).mul_left M) hincr

/-- **GJ §17.5 Lemma 17.5.2 upper bound from geometric increment decay on
covered stages**: the end-to-end conditional capstone.  Given a geometric decay
bound on the consecutive-stage finite-volume β-derivative increments over the
covered exhaustion stages, the derivative-limit provider is constructed and fed
into the concrete compact-ratio infinite-HLS upper-bound assembly, yielding the
named `latticeMass` upper-bound predicate of Lemma 17.5.2 at the right endpoint
`β₂`.

This pins the single remaining analytic input of the GJ §17.5 Lemma 17.5.2
upper-bound side to one quantitative estimate: a summable (here geometric)
convergence-rate bound on the finite-volume β-derivative increments (Issue
#2931, Phase 3).  Besides the standard discrete HLS dimension condition
`2α > d`, the dimension condition `1 ≤ d`, and the distinct-pair condition
`x ≠ z`, all other hypotheses are positivity / high-temperature range
conditions. -/
theorem lemma_17_5_2_upper_bound_of_geometric_increments_on_covered_stages
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hincr :
      ∀ γ₁ γ₂ : ℝ,
        Set.Icc γ₁ γ₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ k : ℕ, ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k →
            ∀ β ∈ Set.Icc γ₁ γ₂,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β) ≤
                M * ratio ^ k) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
  have hprovider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_geometric_increments_on_covered_stages
      Λ J x z M ratio hratio0 hratio1 hincr
  have hd_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := by omega
    exact_mod_cast this
  have hJ2d : 0 < J * ↑(2 * d) := mul_pos hJ_pos hd_pos
  have hβ₂_lt : β₂ < 1 / (J * ↑(2 * d)) := (hIcc ⟨hβ₁₂, le_rfl⟩).2
  have hlt : β₂ * J * ↑(2 * d) < 1 := by
    have h := (lt_div_iff₀ hJ2d).1 hβ₂_lt
    calc β₂ * J * ↑(2 * d) = β₂ * (J * ↑(2 * d)) := by ring
      _ < 1 := h
  exact
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_compact_ratio_bounds_provider
      hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁₂ isOpen_Ioo (subset_refl _) hIcc hβ₁ hβ₁₂ hlt
      (fun β hβ => hβ) hprovider

/-- **GJ §17.5 Lemma 17.5.2 two-sided sandwich from geometric increment decay on
covered stages**: the two-sided analogue of
`lemma_17_5_2_upper_bound_of_geometric_increments_on_covered_stages`.  With the
geometric increment decay supplying the upper side and a validating endpoint
pseudo-mass exponential-decay hypothesis supplying the lower side, the displayed
`latticeMass` sandwich `m⁻(β₂) ≤ m(β₂) ≤ C · m⁻(β₂)` holds for one HLS constant.
Part of Issue #2931. -/
theorem lemma_17_5_2_sandwich_of_geometric_increments_on_covered_stages
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hincr :
      ∀ γ₁ γ₂ : ℝ,
        Set.Icc γ₁ γ₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ k : ℕ, ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k →
            ∀ β ∈ Set.Icc γ₁ γ₂,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β) ≤
                M * ratio ^ k)
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
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
  have hprovider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_geometric_increments_on_covered_stages
      Λ J x z M ratio hratio0 hratio1 hincr
  have hd_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := by omega
    exact_mod_cast this
  have hJ2d : 0 < J * ↑(2 * d) := mul_pos hJ_pos hd_pos
  have hβ₂_lt : β₂ < 1 / (J * ↑(2 * d)) := (hIcc ⟨hβ₁₂, le_rfl⟩).2
  have hlt : β₂ * J * ↑(2 * d) < 1 := by
    have h := (lt_div_iff₀ hJ2d).1 hβ₂_lt
    calc β₂ * J * ↑(2 * d) = β₂ * (J * ↑(2 * d)) := by ring
      _ < 1 := h
  exact
    lemma_17_5_2_sandwich_of_concrete_infinite_hls_compact_ratio_bounds_provider
      hα hαd hd hrho hJ_pos hxz hβ₁₂ isOpen_Ioo (subset_refl _) hIcc hβ₁ hβ₁₂ hlt
      (fun β hβ => hβ) hprovider hdecay

/-- **GJ §17.5 Lemma 17.5.2 capstone from geometric increment decay on covered
stages**: returns the HLS witness and, under the same geometric increment decay
and validating endpoint pseudo-mass decay, both the named upper-bound predicate
and the displayed two-sided `latticeMass` sandwich for one HLS constant.
Part of Issue #2931. -/
theorem lemma_17_5_2_capstone_of_geometric_increments_on_covered_stages
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hincr :
      ∀ γ₁ γ₂ : ℝ,
        Set.Icc γ₁ γ₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ k : ℕ, ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k →
            ∀ β ∈ Set.Icc γ₁ γ₂,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β) ≤
                M * ratio ^ k)
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
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
  have hprovider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_geometric_increments_on_covered_stages
      Λ J x z M ratio hratio0 hratio1 hincr
  have hd_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := by omega
    exact_mod_cast this
  have hJ2d : 0 < J * ↑(2 * d) := mul_pos hJ_pos hd_pos
  have hβ₂_lt : β₂ < 1 / (J * ↑(2 * d)) := (hIcc ⟨hβ₁₂, le_rfl⟩).2
  have hlt : β₂ * J * ↑(2 * d) < 1 := by
    have h := (lt_div_iff₀ hJ2d).1 hβ₂_lt
    calc β₂ * J * ↑(2 * d) = β₂ * (J * ↑(2 * d)) := by ring
      _ < 1 := h
  exact
    lemma_17_5_2_capstone_of_concrete_infinite_hls_compact_ratio_bounds_provider
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc hβ₁ hβ₁₂ hlt
      (fun β hβ => hβ) hprovider hdecay

/-- **GJ §17.5 Lemma 17.5.2 fully-concrete two-sided sandwich from geometric
increment decay and a pseudo-mass high-temperature rate bound**: replaces the
abstract validating exponential-decay hypothesis of
`lemma_17_5_2_sandwich_of_geometric_increments_on_covered_stages` by the concrete
scalar condition `m⁻(β₂) ≤ -log(β₂ J · 2d)`, which validates the endpoint
pseudo-mass as a decay rate via
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate`.

Both sides of the Lemma 17.5.2 sandwich are then driven by concrete scalar
inputs: the geometric β-derivative increment decay (upper) and the pseudo-mass
high-temperature rate bound (lower).  Part of Issue #2931. -/
theorem lemma_17_5_2_sandwich_of_geometric_increments_on_covered_stages_and_pseudoMass_le_rate
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hincr :
      ∀ γ₁ γ₂ : ℝ,
        Set.Icc γ₁ γ₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ k : ℕ, ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k →
            ∀ β ∈ Set.Icc γ₁ γ₂,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β) ≤
                M * ratio ^ k)
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z ≤
        -Real.log (β₂ * J * ↑(2 * d))) :
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
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
  have hβ₂ : 0 < β₂ := (hIcc ⟨hβ₁₂, le_rfl⟩).1
  have hd_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := by omega
    exact_mod_cast this
  have hJ2d : 0 < J * ↑(2 * d) := mul_pos hJ_pos hd_pos
  have hβ₂_lt : β₂ < 1 / (J * ↑(2 * d)) := (hIcc ⟨hβ₁₂, le_rfl⟩).2
  have hlt : β₂ * J * ↑(2 * d) < 1 := by
    have h := (lt_div_iff₀ hJ2d).1 hβ₂_lt
    calc β₂ * J * ↑(2 * d) = β₂ * (J * ↑(2 * d)) := by ring
      _ < 1 := h
  have hdecay :=
    HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hrho Λ hJ_pos.le hβ₂ hlt hle
  exact
    lemma_17_5_2_sandwich_of_geometric_increments_on_covered_stages
      hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
      hincr hdecay

/-- **GJ §17.5 Lemma 17.5.2 fully-concrete capstone from geometric increment
decay and a pseudo-mass high-temperature rate bound**: the capstone counterpart
of
`lemma_17_5_2_sandwich_of_geometric_increments_on_covered_stages_and_pseudoMass_le_rate`,
returning the HLS witness, the named upper-bound predicate, and the two-sided
`latticeMass` sandwich for one HLS constant, with both sides supplied by concrete
scalar inputs.  Part of Issue #2931. -/
theorem lemma_17_5_2_capstone_of_geometric_increments_on_covered_stages_and_pseudoMass_le_rate
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hincr :
      ∀ γ₁ γ₂ : ℝ,
        Set.Icc γ₁ γ₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ k : ℕ, ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k →
            ∀ β ∈ Set.Icc γ₁ γ₂,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β) ≤
                M * ratio ^ k)
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
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
  have hβ₂ : 0 < β₂ := (hIcc ⟨hβ₁₂, le_rfl⟩).1
  have hd_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := by omega
    exact_mod_cast this
  have hJ2d : 0 < J * ↑(2 * d) := mul_pos hJ_pos hd_pos
  have hβ₂_lt : β₂ < 1 / (J * ↑(2 * d)) := (hIcc ⟨hβ₁₂, le_rfl⟩).2
  have hlt : β₂ * J * ↑(2 * d) < 1 := by
    have h := (lt_div_iff₀ hJ2d).1 hβ₂_lt
    calc β₂ * J * ↑(2 * d) = β₂ * (J * ↑(2 * d)) := by ring
      _ < 1 := h
  have hdecay :=
    HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hrho Λ hJ_pos.le hβ₂ hlt hle
  exact
    lemma_17_5_2_capstone_of_geometric_increments_on_covered_stages
      hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
      hincr hdecay

/-! ### Polynomial-prefactor geometric increment bounds

The realistic form of the finite-volume β-derivative increment estimate carries
a polynomial boundary-cardinality prefactor `(2k+3)^d` (the number of fresh
vertices added at stage `k+1` on the cubic exhaustion) times the geometric
distance-decay factor `ratio^k`.  By
`summable_cubicBox_boundary_card_mul_geometric` this prefactored geometric
sequence is still summable, so the covered-stage criterion still produces the
derivative-limit provider and the full Lemma 17.5.2 upper bound / sandwich. -/

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider from a polynomial-prefactor
geometric increment bound on covered stages**: if the consecutive-stage
β-derivative increments over the covered exhaustion stages are bounded by
`M · (2k+3)^d · ratio^k` with `0 ≤ ratio < 1`, then the derivative-limit provider
holds.  The prefactored geometric sequence is summable
(`summable_cubicBox_boundary_card_mul_geometric`), so this is the
boundary-count-aware specialization of
`lemma_17_5_2_derivative_limit_provider_of_summable_increments_on_covered_stages`.
Part of Issue #2931. -/
theorem lemma_17_5_2_derivative_limit_provider_of_poly_geometric_increments_on_covered_stages
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hincr :
      ∀ β₁ β₂ : ℝ,
        Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ k : ℕ, ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k →
            ∀ β ∈ Set.Icc β₁ β₂,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β) ≤
                M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k)) :
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
  lemma_17_5_2_derivative_limit_provider_of_summable_increments_on_covered_stages
    Λ J x z (fun k => M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k))
    ((summable_cubicBox_boundary_card_mul_geometric d hratio0 hratio1).mul_left M) hincr

/-- **GJ §17.5 Lemma 17.5.2 upper bound from a polynomial-prefactor geometric
increment bound on covered stages**: the end-to-end conditional capstone whose
single quantitative input carries the realistic boundary-cardinality prefactor
`(2k+3)^d`.  Builds the derivative-limit provider via
`lemma_17_5_2_derivative_limit_provider_of_poly_geometric_increments_on_covered_stages`
and feeds it into the concrete compact-ratio infinite-HLS upper-bound assembly.
Part of Issue #2931. -/
theorem lemma_17_5_2_upper_bound_of_poly_geometric_increments_on_covered_stages
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hincr :
      ∀ γ₁ γ₂ : ℝ,
        Set.Icc γ₁ γ₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ k : ℕ, ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k →
            ∀ β ∈ Set.Icc γ₁ γ₂,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β) ≤
                M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
  have hprovider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_poly_geometric_increments_on_covered_stages
      Λ J x z M ratio hratio0 hratio1 hincr
  have hd_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := by omega
    exact_mod_cast this
  have hJ2d : 0 < J * ↑(2 * d) := mul_pos hJ_pos hd_pos
  have hβ₂_lt : β₂ < 1 / (J * ↑(2 * d)) := (hIcc ⟨hβ₁₂, le_rfl⟩).2
  have hlt : β₂ * J * ↑(2 * d) < 1 := by
    have h := (lt_div_iff₀ hJ2d).1 hβ₂_lt
    calc β₂ * J * ↑(2 * d) = β₂ * (J * ↑(2 * d)) := by ring
      _ < 1 := h
  exact
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_compact_ratio_bounds_provider
      hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁₂ isOpen_Ioo (subset_refl _) hIcc hβ₁ hβ₁₂ hlt
      (fun β hβ => hβ) hprovider

/-- **GJ §17.5 Lemma 17.5.2 capstone from a polynomial-prefactor geometric
increment bound on covered stages**: returns the HLS witness, the named
upper-bound predicate, and the displayed two-sided `latticeMass` sandwich for one
HLS constant, from the realistic boundary-prefactored increment bound (upper
side) and a validating endpoint pseudo-mass decay (lower side).  Part of Issue
#2931. -/
theorem lemma_17_5_2_capstone_of_poly_geometric_increments_on_covered_stages
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hincr :
      ∀ γ₁ γ₂ : ℝ,
        Set.Icc γ₁ γ₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ k : ℕ, ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k →
            ∀ β ∈ Set.Icc γ₁ γ₂,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β) ≤
                M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k))
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
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
  have hprovider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_poly_geometric_increments_on_covered_stages
      Λ J x z M ratio hratio0 hratio1 hincr
  have hd_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := by omega
    exact_mod_cast this
  have hJ2d : 0 < J * ↑(2 * d) := mul_pos hJ_pos hd_pos
  have hβ₂_lt : β₂ < 1 / (J * ↑(2 * d)) := (hIcc ⟨hβ₁₂, le_rfl⟩).2
  have hlt : β₂ * J * ↑(2 * d) < 1 := by
    have h := (lt_div_iff₀ hJ2d).1 hβ₂_lt
    calc β₂ * J * ↑(2 * d) = β₂ * (J * ↑(2 * d)) := by ring
      _ < 1 := h
  exact
    lemma_17_5_2_capstone_of_concrete_infinite_hls_compact_ratio_bounds_provider
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc hβ₁ hβ₁₂ hlt
      (fun β hβ => hβ) hprovider hdecay

/-- **GJ §17.5 Lemma 17.5.2 fully-concrete capstone from a polynomial-prefactor
geometric increment bound and a pseudo-mass high-temperature rate bound**: the
realistic-form analogue of
`lemma_17_5_2_capstone_of_geometric_increments_on_covered_stages_and_pseudoMass_le_rate`.
Both sides of the Lemma 17.5.2 sandwich are driven by concrete scalar inputs: the
boundary-prefactored geometric β-derivative increment bound
`|F_{k+1}−F_k| ≤ M·(2k+3)^d·ratio^k` (upper) and `m⁻(β₂) ≤ -log(β₂ J · 2d)`
(lower), the latter validating the endpoint pseudo-mass as a decay rate via
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate`.  Part of
Issue #2931. -/
theorem lemma_17_5_2_capstone_of_poly_geometric_increments_on_covered_stages_and_pseudoMass_le_rate
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hincr :
      ∀ γ₁ γ₂ : ℝ,
        Set.Icc γ₁ γ₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ k : ℕ, ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k →
            ∀ β ∈ Set.Icc γ₁ γ₂,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β) ≤
                M * (((2 * k + 3 : ℕ) : ℝ) ^ d * ratio ^ k))
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
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
  have hβ₂ : 0 < β₂ := (hIcc ⟨hβ₁₂, le_rfl⟩).1
  have hd_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := by omega
    exact_mod_cast this
  have hJ2d : 0 < J * ↑(2 * d) := mul_pos hJ_pos hd_pos
  have hβ₂_lt : β₂ < 1 / (J * ↑(2 * d)) := (hIcc ⟨hβ₁₂, le_rfl⟩).2
  have hlt : β₂ * J * ↑(2 * d) < 1 := by
    have h := (lt_div_iff₀ hJ2d).1 hβ₂_lt
    calc β₂ * J * ↑(2 * d) = β₂ * (J * ↑(2 * d)) := by ring
      _ < 1 := h
  have hdecay :=
    HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hrho Λ hJ_pos.le hβ₂ hlt hle
  exact
    lemma_17_5_2_capstone_of_poly_geometric_increments_on_covered_stages
      hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
      hincr hdecay

/-! ## Direct increment API -/

/-- **Direct geometric-increment predicate**, parallel to
`CERouteIccGeometricIncrement` (in `CEConditionalCapstone.lean`) but bypassing
the Cauchy decomposition entirely. This is a named alias for the `hincr`
shape expected by
`lemma_17_5_2_{upper_bound,capstone}_of_geometric_increments_on_covered_stages`.
Useful as a structurally explicit entry point when the user has a direct
increment bound from any non-CE route. -/
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

/-- **Direct poly-geometric-increment predicate**, parallel to the
(now-removed, PR #4301) CE-route poly-geometric increment bundle but
bypassing the Cauchy decomposition. Named alias for the `hincr` shape
expected by
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
