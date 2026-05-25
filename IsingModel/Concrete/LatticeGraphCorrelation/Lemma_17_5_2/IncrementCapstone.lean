import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderFiniteProfile
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderInfiniteHLS

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
      hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁₂ hIcc hβ₁ hβ₁₂ hlt
      (fun β hβ => hβ) hprovider

end Ambient
end IsingModel
