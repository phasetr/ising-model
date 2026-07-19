import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.BetaDerivBridges
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CubicHighTemp

/-!
# GJ §17.5 Lemma 17.5.2 capstone — named-rate and profile-lower capstones

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.Lipschitz` development.
It packages the finite high-temperature enlarged-HLS sandwich and capstone from
the anchored cubic named rate, its interval endpoint forms, and the profile-lower
capstone forms. The heavier entry points carry
`set_option maxHeartbeats 2000000 in` to keep elaboration within budget.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

set_option maxHeartbeats 2000000 in
-- Named-rate entry point for the finite high-temperature enlarged-HLS
-- sandwich package; this avoids unfolding the heavier tanh-profile predicate.
/-- **GJ §17.5 Lemma 17.5.2 finite high-temperature HLS-style sandwich from the
anchored cubic named rate**: active-range membership supplies positivity of the
anchored cubic pseudo-mass, while `cubicOriginNamedRateLeHighTemp` supplies the
lower validating decay input.  The upper side enlarges an HLS convolution
constant enough to dominate the Step 115 path rate.

This is still the finite Step 115/HLS-style package: the enlarged constant may
depend on the current high-temperature parameters and anchored pair. -/
theorem lemma_17_5_2_cubic_high_temp_enlarged_hls_sandwich_of_named_rate
    {α d : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) {r : ℝ} (hr : 0 < r)
    (hd : 0 < d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ≤
        latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
          ENNReal.ofReal
            (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) := by
  obtain ⟨K₀, hK₀, hK₀_conv⟩ := lemma_17_5_2_hls_convolution_constant α d hαd
  let N : ℝ := ((2 * α + 1 : ℕ) : ℝ)
  let m : ℝ := cubicOriginPseudoMassFromParamsAtPair hα hr β J z
  let path : ℝ := -Real.log (Real.tanh (β * J))
  let K : ℝ := max K₀ (path * r / (N * m))
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast Nat.succ_pos (2 * α)
  have hm_pos : 0 < m := by
    dsimp [m]
    exact cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem hα hr hcorr_cubic
  have hK_pos : 0 < K := hK₀.trans_le (le_max_left _ _)
  have hK_conv : ∀ x' y' : Fin d → ℤ,
      ∑' w : Fin d → ℤ,
          (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
          (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K := by
    intro x' y'
    exact (hK₀_conv x' y').trans (le_max_left _ _)
  have hpath_real : path ≤ (N * K / r) * m := by
    have hNm_pos : 0 < N * m := mul_pos hN_pos hm_pos
    have hscale_le : path * r / (N * m) ≤ K := le_max_right _ _
    have hmul_le : path * r ≤ K * (N * m) := by
      have h := mul_le_mul_of_nonneg_right hscale_le hNm_pos.le
      rwa [div_mul_cancel₀ (path * r) hNm_pos.ne'] at h
    have hdiv_le : path ≤ K * (N * m) / r := by
      have h := div_le_div_of_nonneg_right hmul_le hr.le
      rwa [mul_div_cancel_right₀ path hr.ne'] at h
    calc
      path ≤ K * (N * m) / r := hdiv_le
      _ = (N * K / r) * m := by ring
  have hpath_enn :
      ENNReal.ofReal path ≤
        ENNReal.ofReal (N * K / r) * ENNReal.ofReal m := by
    have hcoeff_nonneg : 0 ≤ N * K / r :=
      div_nonneg (mul_nonneg hN_pos.le hK_pos.le) hr.le
    have h := ENNReal.ofReal_le_ofReal hpath_real
    rw [ENNReal.ofReal_mul hcoeff_nonneg] at h
    exact h
  have hlower :=
    cubicNamedRate_capstone_bundle_of_cubicOriginNamedRateLeHighTemp_cubic_corr_mem
      hα hr Λ hJ.le hβ hlt hcorr_cubic hnamed (0 : Fin d → ℤ) z
  refine ⟨K, hK_pos, hK_conv, hlower.1, hlower.2.1.2, ?_⟩
  dsimp [latticeMass]
  apply sSup_le
  rintro b ⟨a, ha, rfl⟩
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  have ha_cubic :
      HasExponentialDecay d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) :=
    HasExponentialDecay_transfer_exhaustion Λ (Ambient.cubicExhaustion d) hf ha
  calc
    (a : ENNReal) ≤ ENNReal.ofReal path :=
      HasExponentialDecay_rate_le_neg_log_tanh_betaJ hd hJ hβ ha_cubic
    _ ≤ ENNReal.ofReal (N * K / r) * ENNReal.ofReal m := hpath_enn
    _ = ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
        ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) := by
      simp [N, m]

set_option maxHeartbeats 2000000 in
-- Interval named-rate entry point: the interval inclusion supplies the endpoint
-- high-temperature scalars for the named-rate enlarged-HLS sandwich.
/-- **GJ §17.5 Lemma 17.5.2 finite high-temperature HLS-style sandwich from an
interval endpoint named rate**: the closed-interval high-temperature inclusion
supplies `0 < β₂` and `β₂ * J * 2d < 1`, so callers only provide the endpoint
active-range and `cubicOriginNamedRateLeHighTemp` inputs at `β₂`. -/
theorem lemma_17_5_2_cubic_high_temp_enlarged_hls_sandwich_of_named_rate_on_Icc
    {α d : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {r : ℝ} (hr : 0 < r) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β₁ β₂ J : ℝ} (hJ : 0 < J) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {z : Fin d → ℤ}
    (hcorr_cubic :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β₂ J z) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
          (cubicOriginPseudoMassFromParamsAtPair hα hr β₂ J z) ∧
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β₂ J z) ≤
        latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
          ENNReal.ofReal
            (cubicOriginPseudoMassFromParamsAtPair hα hr β₂ J z) := by
  have hβ₂_open : β₂ ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) :=
    hIcc (Set.right_mem_Icc.mpr hβ₁₂)
  have h2d_pos : 0 < (↑(2 * d) : ℝ) := by
    have h2d_nat : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast h2d_nat
  have hJ2d_pos : 0 < J * ↑(2 * d) := mul_pos hJ h2d_pos
  have hlt : β₂ * J * ↑(2 * d) < 1 := by
    have hlt' : β₂ * (J * ↑(2 * d)) < 1 :=
      (lt_div_iff₀ hJ2d_pos).mp hβ₂_open.2
    simpa [mul_assoc] using hlt'
  exact
    lemma_17_5_2_cubic_high_temp_enlarged_hls_sandwich_of_named_rate
      (α := α) (d := d) (r := r) (β := β₂) (J := J) (z := z)
      hα hαd hr (Nat.succ_le_iff.mp hd) Λ hJ hβ₂_open.1 hlt hcorr_cubic
      hnamed

set_option maxHeartbeats 2000000 in
-- Repackages the named-rate finite HLS-style sandwich with the matching named
-- upper-bound predicate for the same enlarged HLS constant.
/-- **GJ §17.5 Lemma 17.5.2 named-rate finite HLS-style capstone**:
the endpoint named-rate sandwich wrapper also supplies the matching
`Lemma_17_5_2_UpperBound` predicate for the same enlarged HLS constant `K`.

The displayed sandwich is stated with the target-exhaustion
`pseudoMassFromParamsAtPair`; exhaustion-independence identifies it with the
anchored cubic pseudo-mass used by the named-rate input.  As in the underlying
sandwich theorem, the enlarged constant is finite Step 115/HLS-style data and
may depend on the endpoint parameters and anchored pair. -/
theorem lemma_17_5_2_cubic_high_temp_enlarged_hls_capstone_of_named_rate
    {α d : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) {r : ℝ} (hr : 0 < r)
    (hd : 0 < d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hr Λ J β (0 : Fin d → ℤ) z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) ∧
      HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z) ≤
        latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z) := by
  obtain ⟨K, hK_pos, hconv, hdecay, hlower, hupper_ineq⟩ :=
    lemma_17_5_2_cubic_high_temp_enlarged_hls_sandwich_of_named_rate
      (α := α) (d := d) (r := r) (β := β) (J := J) (z := z)
      hα hαd hr hd Λ hJ hβ hlt hcorr_cubic hnamed
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  have hpm_eq :
      pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z =
        cubicOriginPseudoMassFromParamsAtPair hα hr β J z := by
    calc
      pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z =
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z :=
          pseudoMassFromParamsAtPair_indep_exhaustion hα hr d Λ
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf
            (0 : Fin d → ℤ) z
      _ = cubicOriginPseudoMassFromParamsAtPair hα hr β J z :=
          (cubicOriginPseudoMassFromParamsAtPair_eq hα hr β J z).symm
  have hupper :
      Lemma_17_5_2_UpperBound hα hr Λ J β (0 : Fin d → ℤ) z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) := by
    dsimp [Lemma_17_5_2_UpperBound]
    simpa [hpm_eq] using hupper_ineq
  refine ⟨K, hK_pos, hconv, hupper, ?_, ?_, ?_⟩
  · simpa [hpm_eq] using hdecay
  · simpa [hpm_eq] using hlower
  · simpa [hpm_eq] using hupper_ineq

set_option maxHeartbeats 2000000 in
-- Interval capstone form: the interval inclusion supplies the endpoint
-- high-temperature scalars for the named-rate finite HLS capstone.
/-- **GJ §17.5 Lemma 17.5.2 interval named-rate finite HLS-style capstone**:
the closed-interval high-temperature inclusion supplies the endpoint scalar
inputs, so the endpoint named-rate capstone returns the HLS convolution
constant, the matching `Lemma_17_5_2_UpperBound` predicate, and the displayed
two-sided sandwich at `β₂`. -/
theorem lemma_17_5_2_cubic_high_temp_enlarged_hls_capstone_of_named_rate_on_Icc
    {α d : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {r : ℝ} (hr : 0 < r) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β₁ β₂ J : ℝ} (hJ : 0 < J) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {z : Fin d → ℤ}
    (hcorr_cubic :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β₂ J z) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hr Λ J β₂ (0 : Fin d → ℤ) z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) ∧
      HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z) ≤
        latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z) := by
  have hβ₂_open : β₂ ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) :=
    hIcc (Set.right_mem_Icc.mpr hβ₁₂)
  have h2d_pos : 0 < (↑(2 * d) : ℝ) := by
    have h2d_nat : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast h2d_nat
  have hJ2d_pos : 0 < J * ↑(2 * d) := mul_pos hJ h2d_pos
  have hlt : β₂ * J * ↑(2 * d) < 1 := by
    have hlt' : β₂ * (J * ↑(2 * d)) < 1 :=
      (lt_div_iff₀ hJ2d_pos).mp hβ₂_open.2
    simpa [mul_assoc] using hlt'
  exact
    lemma_17_5_2_cubic_high_temp_enlarged_hls_capstone_of_named_rate
      (α := α) (d := d) (r := r) (β := β₂) (J := J) (z := z)
      hα hαd hr (Nat.succ_le_iff.mp hd) Λ hJ hβ₂_open.1 hlt hcorr_cubic
      hnamed

set_option maxHeartbeats 2000000 in
-- Profile-lower capstone form: the cubic profile comparison supplies the
-- lightweight named-rate premise consumed by the finite HLS capstone.
/-- **GJ §17.5 Lemma 17.5.2 finite HLS-style capstone from a cubic profile
lower bound**: active-range membership and the endpoint cubic profile lower
bound prove the named-rate premise, then the named-rate finite HLS capstone
returns the matching upper-bound predicate and displayed sandwich. -/
theorem lemma_17_5_2_cubic_high_temp_enlarged_hls_capstone_of_profile_lower
    {α d : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) {r : ℝ} (hr : 0 < r)
    (hd : 0 < d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic :
      pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), z}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hr Λ J β (0 : Fin d → ℤ) z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) ∧
      HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z) ≤
        latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z) := by
  have hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z :=
    cubicOriginNamedRateLeHighTemp_of_cubic_pseudoMassG_le_corr
      hα hr hJ.le hβ hlt hcorr_cubic hprofile_cubic
  exact
    lemma_17_5_2_cubic_high_temp_enlarged_hls_capstone_of_named_rate
      (α := α) (d := d) (r := r) (β := β) (J := J) (z := z)
      hα hαd hr hd Λ hJ hβ hlt hcorr_cubic hnamed

/-- **GJ §17.5 Lemma 17.5.2 interval finite HLS-style capstone from a cubic
profile lower bound**: the interval high-temperature inclusion supplies the
endpoint scalar hypotheses at `β₂`, and the endpoint profile-lower capstone
derives the named-rate input before returning the same-constant HLS witness,
upper predicate, validating decay, and displayed two-sided sandwich. -/
theorem lemma_17_5_2_cubic_high_temp_enlarged_hls_capstone_of_profile_lower_on_Icc
    {α d : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {r : ℝ} (hr : 0 < r) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β₁ β₂ J : ℝ} (hJ : 0 < J) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {z : Fin d → ℤ}
    (hcorr_cubic :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic :
      pseudoMassG α r (-Real.log (β₂ * J * ↑(2 * d))) ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), z}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hr Λ J β₂ (0 : Fin d → ℤ) z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) ∧
      HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z) ≤
        latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z) := by
  have hβ₂_open : β₂ ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) :=
    hIcc (Set.right_mem_Icc.mpr hβ₁₂)
  have h2d_pos : 0 < (↑(2 * d) : ℝ) := by
    have h2d_nat : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast h2d_nat
  have hJ2d_pos : 0 < J * ↑(2 * d) := mul_pos hJ h2d_pos
  have hlt : β₂ * J * ↑(2 * d) < 1 := by
    have hlt' : β₂ * (J * ↑(2 * d)) < 1 :=
      (lt_div_iff₀ hJ2d_pos).mp hβ₂_open.2
    simpa [mul_assoc] using hlt'
  exact
    lemma_17_5_2_cubic_high_temp_enlarged_hls_capstone_of_profile_lower
      (α := α) (d := d) (r := r) (β := β₂) (J := J) (z := z)
      hα hαd hr (Nat.succ_le_iff.mp hd) Λ hJ hβ₂_open.1 hlt hcorr_cubic
      hprofile_cubic

end Ambient
end IsingModel
