import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.InfiniteDerivativeLimit
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.Lipschitz

/-!
# GJ §17.5 Lemma 17.5.2 capstone — finite HLS bounds to infinite Lipschitz

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2` development. It
connects the finite-stage HLS derivative bounds, passed through the
finite-to-infinite derivative-limit bridge, to the infinite-volume
HLS-constant Lipschitz package consumed by the upper-bound assembly.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 finite HLS bounds to infinite Lipschitz package**:
under the HLS exponent condition, choose the HLS convolution constant `K`.
If the finite-volume β-derivative profiles converge locally uniformly on the
high-temperature interval and the finite-stage HLS derivative bound for this
same `K` holds eventually and uniformly on `[β₁, β₂]`, then the infinite-volume
HLS Lipschitz estimate for `β ↦ (h β)^(2α+1)` follows.

This composes the interval finite-HLS limit bridge with the existing
infinite-volume pseudo-mass Lipschitz theorem. -/
theorem
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_uniform_finite_deriv_bounds
    {d α : ℕ} (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} (g' : ℝ → ℝ)
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β',
      pseudoMassG α rho (h β') =
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hh_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂,
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            |deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) →
        |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
          ↑(2 * α + 1) * K / rho * (β₂ - β₁)) := by
  let cInf : ℝ → ℝ := fun β' =>
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}
  have hc_diff : ∀ β' ∈ Set.Icc β₁ β₂,
      HasDerivAt cInf (deriv cInf β') β' := by
    intro β hβ
    have hcdiff_g :=
      correlationInfinite_hasDerivAt_beta_of_tendstoLocallyUniformlyOn_deriv
        hd Λ x z hxz J hJ_pos g' hderiv_lim β (hIcc hβ)
    have hderiv_eq : deriv cInf β = g' β := hcdiff_g.deriv
    simpa [cInf, hderiv_eq] using hcdiff_g
  obtain ⟨K, hK, hK_conv, hlip⟩ :=
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_hls_constant
      hαd Λ J x z hβ₁₂ hrho hh_diff hc_diff hh_nonneg hg_eq hh_pos hc_pos
  refine ⟨K, hK, hK_conv, fun hfinite => ?_⟩
  exact hlip
    (lemma_17_5_2_infinite_hls_denominator_comparison_on_Icc_of_uniform_finite_deriv_bounds
      hd Λ J hJ_pos x z hxz β₁ β₂ K hIcc h g' hderiv_lim hfinite)

/-- **GJ §17.5 Lemma 17.5.2 upper bound from a finite-HLS Lipschitz package**:
once the finite-stage HLS bounds have been packaged into the infinite Lipschitz
estimate, the existing all-admissible-rate bridge closes the named upper-bound
predicate for the same selected HLS constant. -/
theorem lemma_17_5_2_upper_bound_of_finite_hls_lipschitz_package
    {d α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) (β₁ β₂ : ℝ) (h : ℝ → ℝ)
    (hpkg :
      ∃ K : ℝ, 0 < K ∧
        (∀ x' y' : Fin d → ℤ,
          ∑' w : Fin d → ℤ,
              (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
              (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
        ((∀ᶠ n in Filter.atTop,
            ∀ β ∈ Set.Icc β₁ β₂,
              |deriv (fun β' =>
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
                K *
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                  (h β) ^ (2 * α)) →
          |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
            ↑(2 * α + 1) * K / r * (β₂ - β₁))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            |deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) →
        Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge
            hα hr Λ J x z β₁ β₂ K h →
          Lemma_17_5_2_UpperBound hα hr Λ J β₂ x z
            (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r))) := by
  obtain ⟨K, hK, hK_conv, hlip⟩ := hpkg
  refine ⟨K, hK, hK_conv, fun hfinite hbridge => ?_⟩
  have hlip_from_denoms :
      (∀ β' ∈ Set.Icc β₁ β₂,
          Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K h) →
        |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
          ↑(2 * α + 1) * K / r * (β₂ - β₁) := by
    intro _hdenom
    exact hlip hfinite
  exact lemma_17_5_2_upper_bound_of_infinite_hls_lipschitz_all_rate_bridge
    hα hr Λ J x z β₁ β₂ K h hlip_from_denoms hbridge

/-- **GJ §17.5 Lemma 17.5.2 sandwich from a finite-HLS Lipschitz package**:
add the lower validating pseudo-mass decay input to the preceding upper-bound
package.  This is the full conditional sandwich assembly after the finite HLS
derivative estimates have been converted to the infinite Lipschitz estimate. -/
theorem lemma_17_5_2_sandwich_of_finite_hls_lipschitz_package
    {d α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J : ℝ} {x z : Fin d → ℤ} {β₁ β₂ : ℝ} {h : ℝ → ℝ}
    (hpkg :
      ∃ K : ℝ, 0 < K ∧
        (∀ x' y' : Fin d → ℤ,
          ∑' w : Fin d → ℤ,
              (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
              (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
        ((∀ᶠ n in Filter.atTop,
            ∀ β ∈ Set.Icc β₁ β₂,
              |deriv (fun β' =>
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
                K *
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                  (h β) ^ (2 * α)) →
          |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
            ↑(2 * α + 1) * K / r * (β₂ - β₁)))
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            |deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) →
        Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge
            hα hr Λ J x z β₁ β₂ K h →
          ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
            ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
          latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
            ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
              ENNReal.ofReal
                (pseudoMassFromParamsAtPair hα hr d Λ
                  (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) := by
  obtain ⟨K, hK, hK_conv, hupper⟩ :=
    lemma_17_5_2_upper_bound_of_finite_hls_lipschitz_package
      hα hr Λ J x z β₁ β₂ h hpkg
  refine ⟨K, hK, hK_conv, fun hfinite hbridge => ?_⟩
  exact lemma_17_5_2_sandwich_of_decay_and_upper hα hr hdecay
    (hupper hfinite hbridge)

/-- **GJ §17.5 Lemma 17.5.2 all-rate bridge from the Step 115 path-rate
comparison**: the named infinite HLS Lipschitz all-rate bridge follows once the
Step 115 path rate `-log(tanh(β₂J))` is bounded by the HLS Lipschitz
coefficient times the endpoint pseudo-mass.

The proof transfers any target-exhaustion validating decay rate to the cubic
exhaustion, applies the all-rate Step 115 bound, and then uses the supplied
scalar comparison. -/
theorem lemma_17_5_2_infinite_hls_lipschitz_all_rate_bridge_of_path_rate_le_hls
    {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (hd : 0 < d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 < J) {β₁ β₂ K : ℝ} (hβ₂ : 0 < β₂)
    (x z : Fin d → ℤ) (h : ℝ → ℝ)
    (hpath_le :
      ENNReal.ofReal (-Real.log (Real.tanh (β₂ * J))) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge
      hα hr Λ J x z β₁ β₂ K h := by
  intro _hlip a ha
  have hf : Ferromagnetic (⟨J, 0, β₂⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ₂⟩
  have ha_cubic :
      HasExponentialDecay d (Ambient.cubicExhaustion d)
        (⟨J, 0, β₂⟩ : IsingParams ℝ) (a : ℝ) :=
    HasExponentialDecay_transfer_exhaustion Λ (Ambient.cubicExhaustion d) hf ha
  exact (HasExponentialDecay_rate_le_neg_log_tanh_betaJ hd hJ hβ₂ ha_cubic).trans
    hpath_le

/-- **GJ §17.5 Lemma 17.5.2 upper bound from finite-HLS Lipschitz and
path-rate comparison**: after the finite HLS derivative estimates have produced
the infinite Lipschitz package, the scalar Step 115 path-rate comparison
discharges the named all-rate bridge and closes the upper-bound predicate. -/
theorem lemma_17_5_2_upper_bound_of_finite_hls_lipschitz_package_and_path_rate_le
    {d α : ℕ} (hα : 1 ≤ α) (hd : 0 < d)
    {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 < J) {x z : Fin d → ℤ} {β₁ β₂ : ℝ}
    (hβ₂ : 0 < β₂) {h : ℝ → ℝ}
    (hpkg :
      ∃ K : ℝ, 0 < K ∧
        (∀ x' y' : Fin d → ℤ,
          ∑' w : Fin d → ℤ,
              (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
              (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
        ((∀ᶠ n in Filter.atTop,
            ∀ β ∈ Set.Icc β₁ β₂,
              |deriv (fun β' =>
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
                K *
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                  (h β) ^ (2 * α)) →
          |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
            ↑(2 * α + 1) * K / r * (β₂ - β₁))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            |deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) →
        ENNReal.ofReal (-Real.log (Real.tanh (β₂ * J))) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
            ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) →
          Lemma_17_5_2_UpperBound hα hr Λ J β₂ x z
            (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r))) := by
  obtain ⟨K, hK, hK_conv, hupper⟩ :=
    lemma_17_5_2_upper_bound_of_finite_hls_lipschitz_package
      hα hr Λ J x z β₁ β₂ h hpkg
  refine ⟨K, hK, hK_conv, fun hfinite hpath_le => ?_⟩
  exact hupper hfinite
    (lemma_17_5_2_infinite_hls_lipschitz_all_rate_bridge_of_path_rate_le_hls
      hα hr hd Λ hJ hβ₂ x z h hpath_le)

/-- **GJ §17.5 Lemma 17.5.2 conditional sandwich from finite-HLS Lipschitz and
path-rate comparison**: combine the preceding path-rate discharge of the
all-rate bridge with the lower validating pseudo-mass decay input. -/
theorem lemma_17_5_2_sandwich_of_finite_hls_lipschitz_package_and_path_rate_le
    {d α : ℕ} (hα : 1 ≤ α) (hd : 0 < d)
    {r : ℝ} (hr : 0 < r)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 < J) {x z : Fin d → ℤ} {β₁ β₂ : ℝ}
    (hβ₂ : 0 < β₂) {h : ℝ → ℝ}
    (hpkg :
      ∃ K : ℝ, 0 < K ∧
        (∀ x' y' : Fin d → ℤ,
          ∑' w : Fin d → ℤ,
              (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
              (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
        ((∀ᶠ n in Filter.atTop,
            ∀ β ∈ Set.Icc β₁ β₂,
              |deriv (fun β' =>
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
                K *
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                  (h β) ^ (2 * α)) →
          |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
            ↑(2 * α + 1) * K / r * (β₂ - β₁)))
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            |deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) →
        ENNReal.ofReal (-Real.log (Real.tanh (β₂ * J))) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
            ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) →
          ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
            ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
          latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
            ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
              ENNReal.ofReal
                (pseudoMassFromParamsAtPair hα hr d Λ
                  (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) := by
  obtain ⟨K, hK, hK_conv, hupper⟩ :=
    lemma_17_5_2_upper_bound_of_finite_hls_lipschitz_package_and_path_rate_le
      hα hd hr Λ hJ hβ₂ hpkg
  refine ⟨K, hK, hK_conv, fun hfinite hpath_le => ?_⟩
  exact lemma_17_5_2_sandwich_of_decay_and_upper hα hr hdecay
    (hupper hfinite hpath_le)

set_option maxHeartbeats 2000000 in
-- The package statement carries the full interval-uniform derivative-limit
-- bridge and an enlarged scalar comparison in one existential.
/-- **GJ §17.5 Lemma 17.5.2 finite-HLS Lipschitz package with an enlarged
path-rate constant**: choose an HLS convolution constant and enlarge it just
enough to dominate the Step 115 path rate at the right endpoint.

The returned constant still carries the HLS convolution inequality.  Its finite
derivative-bound premise is stated for the enlarged constant, and the conclusion
packages both the infinite Lipschitz estimate and the concrete path-rate
comparison needed by the all-rate bridge. -/
theorem
    lemma_17_5_2_enlarged_finite_hls_lipschitz_package_with_path_rate
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} (g' : ℝ → ℝ)
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β',
      pseudoMassG α rho (h β') =
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hh_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂,
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hm_pos :
      0 <
        pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            |deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) →
        |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
          ↑(2 * α + 1) * K / rho * (β₂ - β₁)) ∧
      ENNReal.ofReal (-Real.log (Real.tanh (β₂ * J))) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
  let cInf : ℝ → ℝ := fun β' =>
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}
  have hc_diff : ∀ β' ∈ Set.Icc β₁ β₂,
      HasDerivAt cInf (deriv cInf β') β' := by
    intro β hβ
    have hcdiff_g :=
      correlationInfinite_hasDerivAt_beta_of_tendstoLocallyUniformlyOn_deriv
        (d := d) (Λ := Λ) (r_val := x) (s_val := z) (J := J) (g' := g')
        hd hxz hJ_pos hderiv_lim β (hIcc hβ)
    have hderiv_eq : deriv cInf β = g' β := hcdiff_g.deriv
    simpa [cInf, hderiv_eq] using hcdiff_g
  obtain ⟨K₀, hK₀, hK₀_conv⟩ := lemma_17_5_2_hls_convolution_constant α d hαd
  let N : ℝ := ((2 * α + 1 : ℕ) : ℝ)
  let m : ℝ :=
    pseudoMassFromParamsAtPair hα hrho d Λ
      (⟨J, 0, β₂⟩ : IsingParams ℝ) x z
  let path : ℝ := -Real.log (Real.tanh (β₂ * J))
  let K : ℝ := max K₀ (path * rho / (N * m))
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast Nat.succ_pos (2 * α)
  have hm_pos' : 0 < m := by
    dsimp [m]
    exact hm_pos
  have hK_pos : 0 < K := hK₀.trans_le (le_max_left _ _)
  have hK_conv : ∀ x' y' : Fin d → ℤ,
      ∑' w : Fin d → ℤ,
          (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
          (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K := by
    intro x' y'
    exact (hK₀_conv x' y').trans (le_max_left _ _)
  have hpath_real : path ≤ (N * K / rho) * m := by
    have hNm_pos : 0 < N * m := mul_pos hN_pos hm_pos'
    have hscale_le : path * rho / (N * m) ≤ K := le_max_right _ _
    have hmul_le : path * rho ≤ K * (N * m) := by
      have h := mul_le_mul_of_nonneg_right hscale_le hNm_pos.le
      rwa [div_mul_cancel₀ (path * rho) hNm_pos.ne'] at h
    have hdiv_le : path ≤ K * (N * m) / rho := by
      have h := div_le_div_of_nonneg_right hmul_le hrho.le
      rwa [mul_div_cancel_right₀ path hrho.ne'] at h
    calc
      path ≤ K * (N * m) / rho := hdiv_le
      _ = (N * K / rho) * m := by ring
  have hpath_enn :
      ENNReal.ofReal path ≤ ENNReal.ofReal (N * K / rho) * ENNReal.ofReal m := by
    have hcoeff_nonneg : 0 ≤ N * K / rho :=
      div_nonneg (mul_nonneg hN_pos.le hK_pos.le) hrho.le
    have h := ENNReal.ofReal_le_ofReal hpath_real
    rw [ENNReal.ofReal_mul hcoeff_nonneg] at h
    exact h
  refine ⟨K, hK_pos, hK_conv, ?_, ?_⟩
  · intro hfinite
    exact pseudoMass_pow_succ_lipschitz α hrho hβ₁₂ hh_diff hc_diff hh_nonneg
      hg_eq hh_pos hc_pos
      (lemma_17_5_2_infinite_hls_denominator_comparison_on_Icc_of_uniform_finite_deriv_bounds
        hd Λ J hJ_pos x z hxz β₁ β₂ K hIcc h g' hderiv_lim hfinite)
  · simpa [N, m, path] using hpath_enn

set_option maxHeartbeats 2000000 in
-- Reusing the enlarged finite-HLS existential package requires normalizing a
-- large interval-uniform derivative-bound premise.
/-- **GJ §17.5 Lemma 17.5.2 upper bound from the enlarged finite-HLS package**:
the enlarged constant package removes the separate path-rate comparison premise
from the finite-HLS-to-upper-bound handoff. -/
theorem lemma_17_5_2_upper_bound_of_enlarged_finite_hls_lipschitz_package
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} (g' : ℝ → ℝ)
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β',
      pseudoMassG α rho (h β') =
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hh_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂,
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hm_pos :
      0 <
        pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            |deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) →
          Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
            (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho))) := by
  obtain ⟨K, hK, hK_conv, hlip, hpath_le⟩ :=
    lemma_17_5_2_enlarged_finite_hls_lipschitz_package_with_path_rate
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim
  refine ⟨K, hK, hK_conv, fun hfinite => ?_⟩
  have hd_pos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hbridge :
      Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge
        hα hrho Λ J x z β₁ β₂ K h :=
    lemma_17_5_2_infinite_hls_lipschitz_all_rate_bridge_of_path_rate_le_hls
      hα hrho hd_pos Λ hJ_pos (hIcc (Set.right_mem_Icc.mpr hβ₁₂)).1 x z h
      hpath_le
  exact lemma_17_5_2_upper_bound_of_infinite_hls_lipschitz_all_rate_bridge
    hα hrho Λ J x z β₁ β₂ K h (fun _ => hlip hfinite) hbridge

set_option maxHeartbeats 2000000 in
-- This wrapper reuses the large upper-bound package and preserves its
-- interval-uniform finite derivative premise.
/-- **GJ §17.5 Lemma 17.5.2 sandwich from the enlarged finite-HLS package**:
combine the enlarged finite-HLS upper side with the lower validating
pseudo-mass decay input. -/
theorem lemma_17_5_2_sandwich_of_enlarged_finite_hls_lipschitz_package
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} (g' : ℝ → ℝ)
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β',
      pseudoMassG α rho (h β') =
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hh_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂,
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hm_pos :
      0 <
        pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            |deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) →
          ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hrho d Λ
                (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
            ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
          latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
            ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
              ENNReal.ofReal
                (pseudoMassFromParamsAtPair hα hrho d Λ
                  (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) := by
  obtain ⟨K, hK, hK_conv, hupper⟩ :=
    lemma_17_5_2_upper_bound_of_enlarged_finite_hls_lipschitz_package
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim
  refine ⟨K, hK, hK_conv, fun hfinite => ?_⟩
  exact lemma_17_5_2_sandwich_of_decay_and_upper hα hrho hdecay
    (hupper hfinite)

/-- **GJ §17.5 Lemma 17.5.2 fixed finite derivative bound from a
high-temperature scalar comparison**: for one chosen HLS constant `K`, the
uniform high-temperature finite-stage β-derivative absolute bound supplies the
finite derivative estimate once the scalar Lebowitz/susceptibility bound is
compared with the HLS denominator. -/
theorem lemma_17_5_2_finite_deriv_bound_of_high_temp_scalar_bound
    {d α : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J)
    {a b β₁ β₂ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {x z : Fin d → ℤ} (hxz : x ≠ z) {h : ℝ → ℝ}
    {K : ℝ}
    (hscalar :
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ Set.Icc β₁ β₂,
          let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
          J * M ^ 2 + J * (4 * ↑d) ≤
            K *
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
              (h β) ^ (2 * α)) :
    ∀ᶠ n in Filter.atTop,
      ∀ β ∈ Set.Icc β₁ β₂,
        |deriv (fun β' =>
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
          K *
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
            (h β) ^ (2 * α) := by
  obtain ⟨N, hN⟩ := Λ.exhaust ({x, z} : Finset (Fin d → ℤ))
  filter_upwards [Filter.eventually_ge_atTop N, hscalar] with n hn hscalar_n β hβ
  have hsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume n := hN n hn
  have hx_mem : x ∈ Λ.volume n := hsub (by simp)
  have hz_mem : z ∈ Λ.volume n := hsub (by simp)
  let rx : ↑(Λ.volume n) := ⟨x, hx_mem⟩
  let rz : ↑(Λ.volume n) := ⟨z, hz_mem⟩
  have hrxz : rx ≠ rz := by
    intro heq
    exact hxz (congrArg Subtype.val heq)
  have hlift :
      Ambient.liftFinset ({x, z} : Finset (Fin d → ℤ)) hsub =
        ({rx, rz} : Finset (↑(Λ.volume n))) := by
    ext u
    simp [Ambient.mem_liftFinset, rx, rz, Subtype.ext_iff]
  obtain ⟨dval, hdval, habs⟩ :=
    lemma_17_5_2_beta_deriv_abs_le_high_temp
      Λ J hJ a b ha hab hlt n rx rz hrxz β (hβ_mem β hβ)
  let fAlong : ℝ → ℝ := fun β' =>
    Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n
  let fFinite : ℝ → ℝ := fun β' =>
    IsingModel.correlation
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
      (⟨J, 0, β'⟩ : IsingParams ℝ) {rx, rz}
  have hf_eq : fAlong = fFinite := by
    funext β'
    simp only [fAlong, fFinite]
    rw [Ambient.correlationAlongExhaustion_of_subset
      (G := IsingModel.latticeGraph d) (Λ := Λ)
      (p := (⟨J, 0, β'⟩ : IsingParams ℝ)) hsub, Ambient.correlationΛ_apply,
      hlift]
  have hderiv_along : HasDerivAt fAlong dval β := by
    simpa [fAlong, fFinite, hf_eq] using hdval
  have hderiv_eq :
      deriv (fun β' =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β = dval := by
    simpa [fAlong] using hderiv_along.deriv
  calc
    |deriv (fun β' =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β|
        = |dval| := by rw [hderiv_eq]
    _ ≤ J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d) :=
      habs
    _ ≤ K *
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
        (h β) ^ (2 * α) := by
      simpa using hscalar_n β hβ

/-- **GJ §17.5 Lemma 17.5.2 finite derivative provider from high-temperature
scalar comparisons**: the uniform high-temperature finite-stage β-derivative
absolute bound supplies the derivative-provider input once the scalar
Lebowitz/susceptibility bound is compared with the HLS denominator for every
returned convolution constant. -/
theorem lemma_17_5_2_finite_deriv_provider_of_high_temp_scalar_provider
    {d α : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J)
    {a b β₁ β₂ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {x z : Fin d → ℤ} (hxz : x ≠ z) {h : ℝ → ℝ}
    (hscalar_provider :
      ∀ K : ℝ, 0 < K →
        (∀ x' y' : Fin d → ℤ,
          ∑' w : Fin d → ℤ,
              (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
              (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) →
        ∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
            J * M ^ 2 + J * (4 * ↑d) ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) :
    ∀ K : ℝ, 0 < K →
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) →
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ Set.Icc β₁ β₂,
          |deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
            K *
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
              (h β) ^ (2 * α) := by
  intro K hK hK_conv
  exact lemma_17_5_2_finite_deriv_bound_of_high_temp_scalar_bound
    (d := d) (α := α) (Λ := Λ) (J := J) (a := a) (b := b)
    (β₁ := β₁) (β₂ := β₂) (x := x) (z := z) (h := h) (K := K)
    hJ ha hab hlt hβ_mem hxz (hscalar_provider K hK hK_conv)

/-- **GJ §17.5 Lemma 17.5.2 upper bound from an enlarged finite-HLS package
and a uniform finite derivative-bound provider**: once the finite HLS derivative
estimate is available for every admissible returned convolution constant, the
enlarged package closes the named upper-bound predicate directly. -/
theorem
    lemma_17_5_2_upper_bound_of_enlarged_finite_hls_lipschitz_package_and_deriv_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} (g' : ℝ → ℝ)
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β',
      pseudoMassG α rho (h β') =
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hh_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂,
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hm_pos :
      0 <
        pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hfinite_provider :
      ∀ K : ℝ, 0 < K →
        (∀ x' y' : Fin d → ℤ,
          ∑' w : Fin d → ℤ,
              (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
              (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) →
        ∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            |deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
  obtain ⟨K, hK, hK_conv, hupper⟩ :=
    lemma_17_5_2_upper_bound_of_enlarged_finite_hls_lipschitz_package
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim
  exact ⟨K, hK, hK_conv, hupper (hfinite_provider K hK hK_conv)⟩

/-- **GJ §17.5 Lemma 17.5.2 sandwich from an enlarged finite-HLS package and
a uniform finite derivative-bound provider**: add the lower validating
pseudo-mass decay input to the preceding direct upper-bound assembly. -/
theorem
    lemma_17_5_2_sandwich_of_enlarged_finite_hls_lipschitz_package_and_deriv_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} (g' : ℝ → ℝ)
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β',
      pseudoMassG α rho (h β') =
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hh_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂,
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hm_pos :
      0 <
        pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z))
    (hfinite_provider :
      ∀ K : ℝ, 0 < K →
        (∀ x' y' : Fin d → ℤ,
          ∑' w : Fin d → ℤ,
              (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
              (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) →
        ∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            |deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) :
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
  obtain ⟨K, hK, hK_conv, hupper⟩ :=
    lemma_17_5_2_upper_bound_of_enlarged_finite_hls_lipschitz_package_and_deriv_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim hfinite_provider
  exact ⟨K, hK, hK_conv,
    lemma_17_5_2_sandwich_of_decay_and_upper hα hrho hdecay hupper⟩

/-- **GJ §17.5 Lemma 17.5.2 upper bound from high-temperature scalar
providers**: the high-temperature derivative absolute bound converts scalar
HLS denominator comparisons for every returned constant into the finite
derivative provider consumed by the enlarged finite-HLS package. -/
theorem
    lemma_17_5_2_upper_bound_of_enlarged_finite_hls_lipschitz_package_and_high_temp_scalar_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} (g' : ℝ → ℝ)
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β',
      pseudoMassG α rho (h β') =
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hh_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂,
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hm_pos :
      0 <
        pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hscalar_provider :
      ∀ K : ℝ, 0 < K →
        (∀ x' y' : Fin d → ℤ,
          ∑' w : Fin d → ℤ,
              (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
              (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) →
        ∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
            J * M ^ 2 + J * (4 * ↑d) ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
  exact
    lemma_17_5_2_upper_bound_of_enlarged_finite_hls_lipschitz_package_and_deriv_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim
      (lemma_17_5_2_finite_deriv_provider_of_high_temp_scalar_provider
        (d := d) (α := α) (Λ := Λ) (J := J) (a := a) (b := b)
        (β₁ := β₁) (β₂ := β₂) (x := x) (z := z) (h := h)
        hJ_pos.le ha hab hlt hβ_mem hxz hscalar_provider)

/-- **GJ §17.5 Lemma 17.5.2 sandwich from high-temperature scalar providers**:
add the validating pseudo-mass decay lower side to the preceding scalar-provider
upper-bound assembly. -/
theorem
    lemma_17_5_2_sandwich_of_enlarged_finite_hls_lipschitz_package_and_high_temp_scalar_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} (g' : ℝ → ℝ)
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β',
      pseudoMassG α rho (h β') =
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hh_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂,
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hm_pos :
      0 <
        pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z))
    (hscalar_provider :
      ∀ K : ℝ, 0 < K →
        (∀ x' y' : Fin d → ℤ,
          ∑' w : Fin d → ℤ,
              (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
              (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) →
        ∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
            J * M ^ 2 + J * (4 * ↑d) ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) :
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
  obtain ⟨K, hK, hK_conv, hupper⟩ :=
    lemma_17_5_2_upper_bound_of_enlarged_finite_hls_lipschitz_package_and_high_temp_scalar_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim hscalar_provider
  exact ⟨K, hK, hK_conv,
    lemma_17_5_2_sandwich_of_decay_and_upper hα hrho hdecay hupper⟩

set_option maxHeartbeats 2000000 in
-- The package selects one enlarged constant and normalizes several large
-- interval-uniform derivative and all-rate premises at once.
/-- **GJ §17.5 Lemma 17.5.2 upper bound from a high-temperature ratio lower
bound**: choose a single HLS constant large enough to carry the convolution
bound, dominate the Step 115 path rate, and dominate the high-temperature
Lebowitz/susceptibility scalar bound through an eventual lower bound on
`correlationAlongExhaustion / h^(2α)`. -/
theorem lemma_17_5_2_upper_bound_of_high_temp_ratio_lower
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} (g' : ℝ → ℝ)
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β',
      pseudoMassG α rho (h β') =
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hh_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂,
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hm_pos :
      0 <
        pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    {L : ℝ} (hL_pos : 0 < L)
    (hratio :
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ Set.Icc β₁ β₂,
          L ≤
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
            (h β) ^ (2 * α)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
  let cInf : ℝ → ℝ := fun β' =>
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}
  have hc_diff : ∀ β' ∈ Set.Icc β₁ β₂,
      HasDerivAt cInf (deriv cInf β') β' := by
    intro β hβ
    have hcdiff_g :=
      correlationInfinite_hasDerivAt_beta_of_tendstoLocallyUniformlyOn_deriv
        (d := d) (Λ := Λ) (r_val := x) (s_val := z) (J := J) (g' := g')
        hd hxz hJ_pos hderiv_lim β (hIcc hβ)
    have hderiv_eq : deriv cInf β = g' β := hcdiff_g.deriv
    simpa [cInf, hderiv_eq] using hcdiff_g
  obtain ⟨K₀, hK₀, hK₀_conv⟩ := lemma_17_5_2_hls_convolution_constant α d hαd
  let N : ℝ := ((2 * α + 1 : ℕ) : ℝ)
  let m : ℝ :=
    pseudoMassFromParamsAtPair hα hrho d Λ
      (⟨J, 0, β₂⟩ : IsingParams ℝ) x z
  let path : ℝ := -Real.log (Real.tanh (β₂ * J))
  let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
  let B : ℝ := J * M ^ 2 + J * (4 * ↑d)
  let K : ℝ := max K₀ (max (path * rho / (N * m)) (B / L))
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast Nat.succ_pos (2 * α)
  have hm_pos' : 0 < m := by
    dsimp [m]
    exact hm_pos
  have hK_pos : 0 < K := hK₀.trans_le (le_max_left _ _)
  have hK_conv : ∀ x' y' : Fin d → ℤ,
      ∑' w : Fin d → ℤ,
          (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
          (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K := by
    intro x' y'
    exact (hK₀_conv x' y').trans (le_max_left _ _)
  have hpath_scale : path * rho / (N * m) ≤ K :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hpath_real : path ≤ (N * K / rho) * m := by
    have hNm_pos : 0 < N * m := mul_pos hN_pos hm_pos'
    have hmul_le : path * rho ≤ K * (N * m) := by
      have h := mul_le_mul_of_nonneg_right hpath_scale hNm_pos.le
      rwa [div_mul_cancel₀ (path * rho) hNm_pos.ne'] at h
    have hdiv_le : path ≤ K * (N * m) / rho := by
      have h := div_le_div_of_nonneg_right hmul_le hrho.le
      rwa [mul_div_cancel_right₀ path hrho.ne'] at h
    calc
      path ≤ K * (N * m) / rho := hdiv_le
      _ = (N * K / rho) * m := by ring
  have hpath_enn :
      ENNReal.ofReal path ≤ ENNReal.ofReal (N * K / rho) * ENNReal.ofReal m := by
    have hcoeff_nonneg : 0 ≤ N * K / rho :=
      div_nonneg (mul_nonneg hN_pos.le hK_pos.le) hrho.le
    have h := ENNReal.ofReal_le_ofReal hpath_real
    rw [ENNReal.ofReal_mul hcoeff_nonneg] at h
    exact h
  have hB_le_KL : B ≤ K * L := by
    have hscale : B / L ≤ K :=
      (le_max_right _ _).trans (le_max_right _ _)
    have h := mul_le_mul_of_nonneg_right hscale hL_pos.le
    rwa [div_mul_cancel₀ B hL_pos.ne'] at h
  have hscalar :
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ Set.Icc β₁ β₂,
          let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
          J * M ^ 2 + J * (4 * ↑d) ≤
            K *
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
              (h β) ^ (2 * α) := by
    filter_upwards [hratio] with n hratio_n β hβ
    calc
      J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d)
          = B := by rfl
      _ ≤ K * L := hB_le_KL
      _ ≤ K *
          (Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
            (h β) ^ (2 * α)) :=
          mul_le_mul_of_nonneg_left (hratio_n β hβ) hK_pos.le
      _ = K *
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
          (h β) ^ (2 * α) := by ring
  have hfinite :
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ Set.Icc β₁ β₂,
          |deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
            K *
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
              (h β) ^ (2 * α) :=
    lemma_17_5_2_finite_deriv_bound_of_high_temp_scalar_bound
      (d := d) (α := α) (Λ := Λ) (J := J) (a := a) (b := b)
      (β₁ := β₁) (β₂ := β₂) (x := x) (z := z) (h := h) (K := K)
      hJ_pos.le ha hab hlt hβ_mem hxz hscalar
  have hlip :
      (∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            |deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) →
        |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
          ↑(2 * α + 1) * K / rho * (β₂ - β₁) := by
    intro hfinite'
    exact pseudoMass_pow_succ_lipschitz α hrho hβ₁₂ hh_diff hc_diff hh_nonneg
      hg_eq hh_pos hc_pos
      (lemma_17_5_2_infinite_hls_denominator_comparison_on_Icc_of_uniform_finite_deriv_bounds
        hd Λ J hJ_pos x z hxz β₁ β₂ K hIcc h g' hderiv_lim hfinite')
  have hβ₂_pos : 0 < β₂ := (hIcc (Set.right_mem_Icc.mpr hβ₁₂)).1
  have hd_pos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hbridge :
      Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge
        hα hrho Λ J x z β₁ β₂ K h :=
    lemma_17_5_2_infinite_hls_lipschitz_all_rate_bridge_of_path_rate_le_hls
      hα hrho hd_pos Λ hJ_pos hβ₂_pos x z h
      (by simpa [N, m, path] using hpath_enn)
  exact ⟨K, hK_pos, hK_conv,
    lemma_17_5_2_upper_bound_of_infinite_hls_lipschitz_all_rate_bridge
      hα hrho Λ J x z β₁ β₂ K h (fun _ => hlip hfinite) hbridge⟩

set_option maxHeartbeats 2000000 in
-- This wrapper reuses the large upper-bound package and preserves the same
-- ratio-lower hypotheses while adding the lower validating-decay side.
/-- **GJ §17.5 Lemma 17.5.2 sandwich from a high-temperature ratio lower
bound**: combine the high-temperature ratio-lower upper-bound package with the
validating pseudo-mass decay lower side. -/
theorem lemma_17_5_2_sandwich_of_high_temp_ratio_lower
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} (g' : ℝ → ℝ)
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β',
      pseudoMassG α rho (h β') =
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hh_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂,
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hm_pos :
      0 <
        pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z))
    {L : ℝ} (hL_pos : 0 < L)
    (hratio :
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ Set.Icc β₁ β₂,
          L ≤
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
            (h β) ^ (2 * α)) :
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
  obtain ⟨K, hK, hK_conv, hupper⟩ :=
    lemma_17_5_2_upper_bound_of_high_temp_ratio_lower
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim hL_pos hratio
  exact ⟨K, hK, hK_conv,
    lemma_17_5_2_sandwich_of_decay_and_upper hα hrho hdecay hupper⟩

end Ambient
end IsingModel
