import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.BetaDerivBridges
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CubicHighTemp

/-!
# GJ §17.5 Lemma 17.5.2 capstone — cubic enlarged-HLS sandwich packages

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.Lipschitz` development.
It assembles the cubic high-temperature HLS-constant conditional sandwich and the
finite Step 115/HLS enlarged-constant sandwich and capstone packages, for the
anchored origin pair and for arbitrary cubic pairs, including the interval forms.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 cubic high-temperature HLS-constant conditional
sandwich**: combine the existing cubic high-temperature lower-bound capstone
with the HLS convolution constant package. The remaining HLS input is exactly
the all-admissible-decay-rate estimate for the returned constant `K`.

This is the concrete cubic-exhaustion version of the HLS route toward the full
Lemma 17.5.2 sandwich. It keeps the final analytic/HLS all-rate estimate as an
explicit premise, rather than claiming the book's HLS-uniform upper side is
already proved. -/
theorem lemma_17_5_2_cubic_high_temp_hls_conditional_sandwich
    {α d : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hinputs :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2 ∧
        pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
          Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              {(0 : Fin d → ℤ), z}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ a : NNReal,
          HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) →
            (a : ENNReal) ≤
              ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
                ENNReal.ofReal
                  (cubicOriginPseudoMassFromParamsAtPair hα hr β J z)) →
        HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
        ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ≤
          latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
        latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
            ENNReal.ofReal
              (cubicOriginPseudoMassFromParamsAtPair hα hr β J z)) := by
  obtain ⟨K, hK, hK_conv⟩ := lemma_17_5_2_hls_convolution_constant α d hαd
  refine ⟨K, hK, hK_conv, fun hdecay_le => ?_⟩
  have hlower :=
    lemma_17_5_2_cubic_high_temp_lower_capstone hα hr Λ hJ hβ hlt hinputs
  refine ⟨hlower.1, hlower.2.2, ?_⟩
  dsimp [latticeMass]
  apply sSup_le
  rintro b ⟨a, ha, rfl⟩
  exact hdecay_le a ha

/-- **GJ §17.5 Lemma 17.5.2 cubic high-temperature HLS sandwich from a
path-rate scalar comparison**: after choosing the HLS convolution constant,
the Step 115 all-rate path bound discharges the all-admissible-decay-rate
premise of `lemma_17_5_2_cubic_high_temp_hls_conditional_sandwich` whenever
`-log(tanh(βJ))` is bounded by the HLS coefficient times the anchored cubic
pseudo-mass.

This isolates the remaining upper-bound task to a scalar comparison between
the Step 115 path rate and the HLS Lipschitz coefficient. -/
theorem lemma_17_5_2_cubic_high_temp_hls_sandwich_of_path_rate_le_hls
    {α d : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) {r : ℝ} (hr : 0 < r)
    (hd : 0 < d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hinputs :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2 ∧
        pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
          Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              {(0 : Fin d → ℤ), z}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      (ENNReal.ofReal (-Real.log (Real.tanh (β * J))) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
            ENNReal.ofReal
              (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) →
        HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
        ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ≤
          latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
        latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
            ENNReal.ofReal
              (cubicOriginPseudoMassFromParamsAtPair hα hr β J z)) := by
  obtain ⟨K, hK, hK_conv, hfinish⟩ :=
    lemma_17_5_2_cubic_high_temp_hls_conditional_sandwich
      hα hαd hr Λ hJ.le hβ hlt hinputs
  refine ⟨K, hK, hK_conv, fun hpath_le => hfinish ?_⟩
  intro a ha
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  have ha_cubic :
      HasExponentialDecay d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) :=
    HasExponentialDecay_transfer_exhaustion Λ (Ambient.cubicExhaustion d) hf ha
  exact (HasExponentialDecay_rate_le_neg_log_tanh_betaJ hd hJ hβ ha_cubic).trans hpath_le

/-- **GJ §17.5 Lemma 17.5.2 finite high-temperature HLS-style sandwich with
an enlarged constant**: in the cubic high-temperature active range, enlarge a
discrete HLS convolution constant enough to dominate the Step 115 path rate.
The resulting constant simultaneously carries the HLS convolution inequality
and gives the full `ofReal m⁻ ≤ latticeMass ≤ C · ofReal m⁻` sandwich.

The constant may depend on the current high-temperature parameters and the
anchored pair; this is the finite Step 115/HLS package, not the book's final
uniform HLS constant. -/
theorem lemma_17_5_2_cubic_high_temp_enlarged_hls_sandwich
    {α d : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) {r : ℝ} (hr : 0 < r)
    (hd : 0 < d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hinputs :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2 ∧
        pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
          Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              {(0 : Fin d → ℤ), z}) :
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
    exact cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem hα hr hinputs.1
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
    lemma_17_5_2_cubic_high_temp_lower_capstone hα hr Λ hJ.le hβ hlt hinputs
  refine ⟨K, hK_pos, hK_conv, hlower.1, hlower.2.2, ?_⟩
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

/-- **GJ §17.5 Lemma 17.5.2 finite high-temperature HLS-style sandwich for
an arbitrary cubic pair**: in the cubic high-temperature active range, enlarge
a discrete HLS convolution constant enough to dominate the Step 115 path rate
for the pair pseudo-mass attached to `{x,z}`.  The returned constant carries
the HLS convolution inequality and gives the target-exhaustion sandwich
`ofReal m⁻ ≤ latticeMass ≤ C · ofReal m⁻`, with
`m⁻ := pseudoMassFromParamsAtPair ... Λ ... x z`.

As with `lemma_17_5_2_cubic_high_temp_enlarged_hls_sandwich`, the enlarged
constant may depend on the parameters and the pair; it is a finite
Step 115/HLS package, not the book's final uniform HLS constant. -/
theorem lemma_17_5_2_cubic_pair_high_temp_enlarged_hls_sandwich
    {α d : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) {r : ℝ} (hr : 0 < r)
    (hd : 0 < d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hinputs :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
            ∈ Set.Ioo (0 : ℝ) 2 ∧
        pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
          Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z) ≤
        latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  obtain ⟨K₀, hK₀, hK₀_conv⟩ := lemma_17_5_2_hls_convolution_constant α d hαd
  let N : ℝ := ((2 * α + 1 : ℕ) : ℝ)
  let p : IsingParams ℝ := ⟨J, 0, β⟩
  let m₀ : ℝ := pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d) p x z
  let path : ℝ := -Real.log (Real.tanh (β * J))
  let K : ℝ := max K₀ (path * r / (N * m₀))
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  have hm_eq :
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z = m₀ := by
    dsimp [m₀, p]
    exact pseudoMassFromParamsAtPair_indep_exhaustion hα hr d Λ
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf x z
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast Nat.succ_pos (2 * α)
  have hm_pos : 0 < m₀ := by
    dsimp [m₀, p]
    exact pseudoMassFromParamsAtPair_pos_of_corr_mem hα hr d
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) x z hinputs.1
  have hK_pos : 0 < K := hK₀.trans_le (le_max_left _ _)
  have hK_conv : ∀ x' y' : Fin d → ℤ,
      ∑' w : Fin d → ℤ,
          (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
          (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K := by
    intro x' y'
    exact (hK₀_conv x' y').trans (le_max_left _ _)
  have hpath_real : path ≤ (N * K / r) * m₀ := by
    have hNm_pos : 0 < N * m₀ := mul_pos hN_pos hm_pos
    have hscale_le : path * r / (N * m₀) ≤ K := le_max_right _ _
    have hmul_le : path * r ≤ K * (N * m₀) := by
      have h := mul_le_mul_of_nonneg_right hscale_le hNm_pos.le
      rwa [div_mul_cancel₀ (path * r) hNm_pos.ne'] at h
    have hdiv_le : path ≤ K * (N * m₀) / r := by
      have h := div_le_div_of_nonneg_right hmul_le hr.le
      rwa [mul_div_cancel_right₀ path hr.ne'] at h
    calc
      path ≤ K * (N * m₀) / r := hdiv_le
      _ = (N * K / r) * m₀ := by ring
  have hpath_enn :
      ENNReal.ofReal path ≤
        ENNReal.ofReal (N * K / r) * ENNReal.ofReal m₀ := by
    have hcoeff_nonneg : 0 ≤ N * K / r :=
      div_nonneg (mul_nonneg hN_pos.le hK_pos.le) hr.le
    have h := ENNReal.ofReal_le_ofReal hpath_real
    rw [ENNReal.ofReal_mul hcoeff_nonneg] at h
    exact h
  have hlower :=
    lemma_17_5_2_cubic_pair_high_temp_lower_capstone hα hr Λ hJ.le hβ hlt hinputs
  refine ⟨K, hK_pos, hK_conv, ?_, ?_, ?_⟩
  · simpa [hm_eq, m₀, p] using hlower.1
  · simpa [hm_eq, m₀, p] using hlower.2
  · dsimp [latticeMass]
    apply sSup_le
    rintro b ⟨a, ha, rfl⟩
    have ha_cubic :
        HasExponentialDecay d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) :=
      HasExponentialDecay_transfer_exhaustion Λ (Ambient.cubicExhaustion d) hf ha
    calc
      (a : ENNReal) ≤ ENNReal.ofReal path :=
        HasExponentialDecay_rate_le_neg_log_tanh_betaJ hd hJ hβ ha_cubic
      _ ≤ ENNReal.ofReal (N * K / r) * ENNReal.ofReal m₀ := hpath_enn
      _ = ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
        simp [N, m₀, p, hm_eq]

/-- **GJ §17.5 Lemma 17.5.2 finite high-temperature HLS-style capstone for an
arbitrary cubic pair**: repackages the arbitrary-pair enlarged-HLS sandwich so
that downstream callers receive, for the same enlarged constant `K`, the HLS
convolution inequality, the named `Lemma_17_5_2_UpperBound` predicate, the
target-exhaustion validating decay, and the displayed two-sided sandwich. -/
theorem lemma_17_5_2_cubic_pair_high_temp_enlarged_hls_capstone
    {α d : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) {r : ℝ} (hr : 0 < r)
    (hd : 0 < d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hinputs :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
            ∈ Set.Ioo (0 : ℝ) 2 ∧
        pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
          Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hr Λ J β x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) ∧
      HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z) ≤
        latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  obtain ⟨K, hK, hK_conv, hdecay, hlower, hupper_ineq⟩ :=
    lemma_17_5_2_cubic_pair_high_temp_enlarged_hls_sandwich
      (α := α) (d := d) (r := r) (β := β) (J := J) (x := x) (z := z)
      hα hαd hr hd Λ hJ hβ hlt hinputs
  have hupper :
      Lemma_17_5_2_UpperBound hα hr Λ J β x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) := by
    dsimp [Lemma_17_5_2_UpperBound]
    exact hupper_ineq
  exact ⟨K, hK, hK_conv, hupper, hdecay, hlower, hupper_ineq⟩

/-- **GJ §17.5 Lemma 17.5.2 interval finite high-temperature HLS-style
sandwich for an arbitrary cubic pair**: the closed-interval high-temperature
inclusion supplies the endpoint scalar hypotheses at `β₂`, then the endpoint
arbitrary-pair enlarged-HLS sandwich returns the target-exhaustion displayed
sandwich for `{x,z}`. -/
theorem lemma_17_5_2_cubic_pair_high_temp_enlarged_hls_sandwich_on_Icc
    {α d : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {r : ℝ} (hr : 0 < r) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β₁ β₂ J : ℝ} (hJ : 0 < J) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {x z : Fin d → ℤ}
    (hinputs :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ) {x, z}
            ∈ Set.Ioo (0 : ℝ) 2 ∧
        pseudoMassG α r (-Real.log (β₂ * J * ↑(2 * d))) ≤
          Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ) {x, z}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) ≤
        latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
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
    lemma_17_5_2_cubic_pair_high_temp_enlarged_hls_sandwich
      (α := α) (d := d) (r := r) (β := β₂) (J := J) (x := x) (z := z)
      hα hαd hr (Nat.succ_le_iff.mp hd) Λ hJ hβ₂_open.1 hlt hinputs

/-- **GJ §17.5 Lemma 17.5.2 interval finite high-temperature HLS-style
capstone for an arbitrary cubic pair**: the interval high-temperature inclusion
supplies `0 < β₂` and `β₂ * J * 2d < 1`, and the endpoint arbitrary-pair
capstone then returns the same-constant HLS convolution witness, named upper
predicate, target-exhaustion validating decay, and displayed two-sided
sandwich. -/
theorem lemma_17_5_2_cubic_pair_high_temp_enlarged_hls_capstone_on_Icc
    {α d : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {r : ℝ} (hr : 0 < r) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β₁ β₂ J : ℝ} (hJ : 0 < J) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {x z : Fin d → ℤ}
    (hinputs :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ) {x, z}
            ∈ Set.Ioo (0 : ℝ) 2 ∧
        pseudoMassG α r (-Real.log (β₂ * J * ↑(2 * d))) ≤
          Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ) {x, z}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hr Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) ∧
      HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) ≤
        latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
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
    lemma_17_5_2_cubic_pair_high_temp_enlarged_hls_capstone
      (α := α) (d := d) (r := r) (β := β₂) (J := J) (x := x) (z := z)
      hα hαd hr (Nat.succ_le_iff.mp hd) Λ hJ hβ₂_open.1 hlt hinputs

end Ambient
end IsingModel
