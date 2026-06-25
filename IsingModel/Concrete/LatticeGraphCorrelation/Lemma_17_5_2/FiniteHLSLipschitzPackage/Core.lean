import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.InfiniteDerivativeLimit
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.Lipschitz
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PathRateBridge
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempLipschitz.UniformDiff

/-!
# GJ §17.5 Lemma 17.5.2 finite-HLS Lipschitz package -- core and path-rate wrappers

Part of the split `FiniteHLSLipschitzPackage` layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

/-- **Endpoint scalar bounds from a high-temperature interval inclusion**:
if the closed beta interval is contained in the high-temperature region, then
both endpoints are positive and the right endpoint satisfies `β₂ * J * 2d < 1`.
-/
theorem lemma_17_5_2_interval_endpoints_of_Icc_subset_high_temp
    {d : ℕ} (hd : 1 ≤ d) {J β₁ β₂ : ℝ} (hJ_pos : 0 < J)
    (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) :
    0 < β₁ ∧ 0 < β₂ ∧ β₂ * J * ↑(2 * d) < 1 := by
  have hβ₁_open : β₁ ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) :=
    hIcc (Set.left_mem_Icc.mpr hβ₁₂)
  have hβ₂_open : β₂ ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) :=
    hIcc (Set.right_mem_Icc.mpr hβ₁₂)
  refine ⟨hβ₁_open.1, hβ₂_open.1, ?_⟩
  have h2d_pos : 0 < (↑(2 * d) : ℝ) := by
    have h2d_nat : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast h2d_nat
  have hJ2d_pos : 0 < J * ↑(2 * d) := mul_pos hJ_pos h2d_pos
  have hlt : β₂ * (J * ↑(2 * d)) < 1 := by
    exact (lt_div_iff₀ hJ2d_pos).mp hβ₂_open.2
  simpa [mul_assoc] using hlt

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
    {s : Set ℝ} (hs_open : IsOpen s)
    (hs_sub : s ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hIcc : Set.Icc β₁ β₂ ⊆ s)
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} (g' : ℝ → ℝ)
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β' ∈ Set.Icc β₁ β₂,
      (fun γ => pseudoMassG α rho (h γ)) =ᶠ[nhds β']
        (fun γ =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, γ⟩ : IsingParams ℝ) {x, z}))
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
        g' Filter.atTop s) :
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
        hd Λ x z hxz J hJ_pos g' hs_open hs_sub hderiv_lim β (hIcc hβ)
    have hderiv_eq : deriv cInf β = g' β := hcdiff_g.deriv
    simpa [cInf, hderiv_eq] using hcdiff_g
  obtain ⟨K, hK, hK_conv, hlip⟩ :=
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_hls_constant
      hαd Λ J x z hβ₁₂ hrho hh_diff hc_diff hh_nonneg
      hg_eq hh_pos hc_pos
  refine ⟨K, hK, hK_conv, fun hfinite => ?_⟩
  exact hlip
    (lemma_17_5_2_infinite_hls_denominator_comparison_on_Icc_of_uniform_finite_deriv_bounds
      hd Λ J hJ_pos x z hxz β₁ β₂ K hs_open hs_sub hIcc h g' hderiv_lim hfinite)

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

/-- **GJ §17.5 Lemma 17.5.2 interval upper bound from finite-HLS Lipschitz and
path-rate comparison**: the closed-interval high-temperature inclusion supplies
the endpoint positivity needed by the path-rate all-rate bridge, so callers can
use the same interval hypothesis as the later enlarged finite-HLS packages. -/
theorem
    lemma_17_5_2_upper_bound_of_finite_hls_lipschitz_package_and_path_rate_le_on_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d)
    {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 < J) {x z : Fin d → ℤ} {β₁ β₂ : ℝ}
    (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {h : ℝ → ℝ}
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
  have hβ₂_pos : 0 < β₂ := (hIcc (Set.right_mem_Icc.mpr hβ₁₂)).1
  exact
    lemma_17_5_2_upper_bound_of_finite_hls_lipschitz_package_and_path_rate_le
      hα (Nat.succ_le_iff.mp hd) hr Λ hJ hβ₂_pos hpkg

/-- **GJ §17.5 Lemma 17.5.2 interval sandwich from finite-HLS Lipschitz and
path-rate comparison**: combine the interval-facing upper wrapper with the
lower validating pseudo-mass decay input. -/
theorem
    lemma_17_5_2_sandwich_of_finite_hls_lipschitz_package_and_path_rate_le_on_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d)
    {r : ℝ} (hr : 0 < r)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 < J) {x z : Fin d → ℤ} {β₁ β₂ : ℝ}
    (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {h : ℝ → ℝ}
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
  have hβ₂_pos : 0 < β₂ := (hIcc (Set.right_mem_Icc.mpr hβ₁₂)).1
  exact
    lemma_17_5_2_sandwich_of_finite_hls_lipschitz_package_and_path_rate_le
      hα (Nat.succ_le_iff.mp hd) hr hJ hβ₂_pos hpkg hdecay

end Ambient
end IsingModel
