import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.Predicates
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferCubicPseudoMassCorr

/-!
# GJ §17.5 Lemma 17.5.2 capstone — cubic high-temperature bridges

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2` development. It
collects the cubic-exhaustion high-temperature analogues of Lemma 17.5.2:
the lower-bound capstone derived from the bundled active-range plus
`cubicTanhProfileBound` inputs, the positivity capstone for `latticeMass`, the
finite-stage Step 115 upper-bound bridge discharging the named upper-bound
predicate at the constant `-log(tanh(βJ)) / m⁻`, and the resulting finite
sandwich capstone.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.1, pp.~304--306;
  §17.5, pp.~310--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 lower-bound capstone, cubic high-temperature
form**: on the cubic exhaustion at high temperature `β·J·(2d) < 1`,
combined with the bundled active-range plus tanh-power profile inputs at
the anchored cubic pair `{0, z}`, the named anchored cubic pseudo-mass
`m⁻ := cubicOriginPseudoMassFromParamsAtPair` validates exponential decay
and satisfies the lower-bound interval membership
`ENNReal.ofReal m⁻ ∈ (0, latticeMass]` against every target exhaustion.

This is the Lemma 17.5.2 lower-bound side specialised to the regime where
both the active-range and the high-temperature comparison are available
from the existing `cubicTanhProfileBound` infrastructure; the upper-bound
side (a future Lipschitz + HLS PR) is not addressed here.

References: Glimm--Jaffe §17.1, pp.~304--306 and §17.5 Lemma 17.5.2,
pp.~311--312. -/
theorem lemma_17_5_2_cubic_high_temp_lower_capstone
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
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
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
        Set.Ioc (0 : ENNReal) (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) := by
  have hbundle :=
    cubicNamedRate_capstone_bundle_of_cubic_corr_mem_Ioo_and_profile
      hα hr Λ hJ hβ hlt hinputs (0 : Fin d → ℤ) z
  exact ⟨hbundle.1, hbundle.2.1⟩

/-- **GJ §17.5 Lemma 17.5.2 lower-bound capstone, cubic pair form**:
for an arbitrary pair `{x,z}` on the cubic exhaustion, the active-range plus
tanh-power profile inputs make the cubic-reference pair pseudo-mass a
validating decay rate for every target exhaustion, and place that rate below
the target `latticeMass`.

This is the pair-general reference-exhaustion version of
`lemma_17_5_2_cubic_high_temp_lower_capstone`; the origin-anchored wrapper is a
convenient special case used by the named cubic pseudo-mass API.

References: Glimm--Jaffe §17.1, pp.~304--306 and §17.5 Lemma 17.5.2,
pp.~311--312. -/
theorem lemma_17_5_2_cubic_pair_high_temp_lower_capstone
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hinputs :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
            ∈ Set.Ioo (0 : ℝ) 2 ∧
        pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
          Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        (pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  exact ⟨
    HasExponentialDecay_cubic_pseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
      hα hr Λ hJ hβ hlt hinputs.1 hinputs.2,
    latticeMass_ge_cubic_pseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
      hα hr Λ hJ hβ hlt hinputs.1 hinputs.2⟩

/-- **GJ §17.5 Lemma 17.5.2 cubic high-temperature `latticeMass` positivity
capstone**: under the same active-range + tanh-power profile inputs as
`lemma_17_5_2_cubic_high_temp_lower_capstone`, every target exhaustion has
strictly positive lattice mass.

Reference: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
theorem lemma_17_5_2_cubic_high_temp_latticeMass_pos
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
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
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  have hbundle :=
    cubicNamedRate_capstone_bundle_of_cubic_corr_mem_Ioo_and_profile
      hα hr Λ hJ hβ hlt hinputs (0 : Fin d → ℤ) z
  exact hbundle.2.2.1

/-- **GJ §17.5 Lemma 17.5.2 finite upper-bound bridge, cubic
high-temperature form**: if the anchored cubic two-point input lies in the
active interval `(0,2)`, then the upper-bound predicate from the conditional
capstone is discharged by the finite Step 115 constant
`-log(tanh (βJ)) / m⁻`, where
`m⁻ := cubicOriginPseudoMassFromParamsAtPair`.

This is not the HLS-uniform constant from the proof of GJ Theorem 17.5.1.
It is a finite high-temperature bridge using the already-formalized
`latticeMass ≤ -log(tanh(βJ))` bound, exhaustion-independence of
`latticeMass`, and strict positivity of the active-range pseudo-mass.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312; Step 115
upper bound on the lattice mass. -/
theorem lemma_17_5_2_cubic_high_temp_upper_bound_of_active_range
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (hd : 0 < d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 < J) (hβ : 0 < β) {z : Fin d → ℤ}
    (hcorr_cubic :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2) :
    Lemma_17_5_2_UpperBound hα hr Λ J β (0 : Fin d → ℤ) z
      (ENNReal.ofReal
        (-Real.log (Real.tanh (β * J)) /
          cubicOriginPseudoMassFromParamsAtPair hα hr β J z)) := by
  dsimp [Lemma_17_5_2_UpperBound]
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
  rw [hpm_eq]
  have hpm_pos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z :=
    cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem hα hr hcorr_cubic
  have hpm_ne_zero :
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hpm_pos)
  have hmul :
      ENNReal.ofReal
          (-Real.log (Real.tanh (β * J)) /
            cubicOriginPseudoMassFromParamsAtPair hα hr β J z) *
        ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) =
          ENNReal.ofReal (-Real.log (Real.tanh (β * J))) := by
    rw [ENNReal.ofReal_div_of_pos hpm_pos]
    exact ENNReal.div_mul_cancel hpm_ne_zero ENNReal.ofReal_ne_top
  calc
    latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        = latticeMass d (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) :=
          latticeMass_indep_cubicExhaustion Λ hf
    _ ≤ ENNReal.ofReal (-Real.log (Real.tanh (β * J))) :=
          latticeMass_le_neg_log_tanh_betaJ hd hJ hβ
    _ = ENNReal.ofReal
          (-Real.log (Real.tanh (β * J)) /
            cubicOriginPseudoMassFromParamsAtPair hα hr β J z) *
        ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) :=
          hmul.symm

/-- **GJ §17.5 Lemma 17.5.2 finite all-rate upper bridge, cubic
high-temperature form**: the finite Step 115 upper-bound bridge also controls
every admissible nonnegative exponential decay rate. This is the all-rate
target shape consumed by the order-theoretic upper-bound assembly.

The constant is the finite high-temperature constant
`-log(tanh(βJ)) / m⁻`, not the HLS-uniform constant from the book.  The proof
uses the Step 115 all-rate path bound directly, rather than first closing a
`latticeMass` upper-bound predicate and converting it back to an all-rate
estimate. -/
theorem lemma_17_5_2_cubic_high_temp_all_decay_rates_le_of_active_range
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (hd : 0 < d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 < J) (hβ : 0 < β) {z : Fin d → ℤ}
    (hcorr_cubic :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (a : NNReal)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ)) :
    (a : ENNReal) ≤
      ENNReal.ofReal
          (-Real.log (Real.tanh (β * J)) /
            cubicOriginPseudoMassFromParamsAtPair hα hr β J z) *
        ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) := by
  have hpm_pos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z :=
    cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem hα hr hcorr_cubic
  have hpm_ne_zero :
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hpm_pos)
  have hmul :
      ENNReal.ofReal
          (-Real.log (Real.tanh (β * J)) /
            cubicOriginPseudoMassFromParamsAtPair hα hr β J z) *
        ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) =
          ENNReal.ofReal (-Real.log (Real.tanh (β * J))) := by
    rw [ENNReal.ofReal_div_of_pos hpm_pos]
    exact ENNReal.div_mul_cancel hpm_ne_zero ENNReal.ofReal_ne_top
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  have hdecay_cubic :
      HasExponentialDecay d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) :=
    HasExponentialDecay_transfer_exhaustion Λ (Ambient.cubicExhaustion d) hf hdecay
  calc
    (a : ENNReal) ≤ ENNReal.ofReal (-Real.log (Real.tanh (β * J))) :=
      HasExponentialDecay_rate_le_neg_log_tanh_betaJ hd hJ hβ hdecay_cubic
    _ = ENNReal.ofReal
          (-Real.log (Real.tanh (β * J)) /
            cubicOriginPseudoMassFromParamsAtPair hα hr β J z) *
        ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) :=
      hmul.symm

/-- **GJ §17.5 Lemma 17.5.2 finite sandwich capstone, cubic high-temperature
form**: combining the existing cubic lower-bound capstone with the finite
Step 115 upper-bound bridge gives an actual two-sided sandwich
`ofReal m⁻ ≤ latticeMass ≤ C_fin · ofReal m⁻` for every target exhaustion,
where `m⁻ := cubicOriginPseudoMassFromParamsAtPair` and
`C_fin = -log(tanh(βJ)) / m⁻`.

The lower side still uses the same active-range plus tanh-power profile inputs
as `lemma_17_5_2_cubic_high_temp_lower_capstone`. The upper side uses only
the active-range positivity, the high-temperature Step 115 mass upper bound,
and exhaustion-independence. This closes the existing Lean upper-bound
predicate with a finite high-temperature constant, while deliberately not
claiming the HLS-uniform constant from the book.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
theorem lemma_17_5_2_cubic_high_temp_sandwich_capstone
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (hd : 0 < d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
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
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ≤
        latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal
          (-Real.log (Real.tanh (β * J)) /
            cubicOriginPseudoMassFromParamsAtPair hα hr β J z) *
          ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) := by
  have hlower :=
    lemma_17_5_2_cubic_high_temp_lower_capstone hα hr Λ hJ.le hβ hlt hinputs
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  have hpm_pos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z :=
    cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem hα hr hinputs.1
  have hpm_ne_zero :
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hpm_pos)
  have hmul :
      ENNReal.ofReal
          (-Real.log (Real.tanh (β * J)) /
            cubicOriginPseudoMassFromParamsAtPair hα hr β J z) *
        ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) =
          ENNReal.ofReal (-Real.log (Real.tanh (β * J))) := by
    rw [ENNReal.ofReal_div_of_pos hpm_pos]
    exact ENNReal.div_mul_cancel hpm_ne_zero ENNReal.ofReal_ne_top
  refine ⟨hlower.1, hlower.2.2, ?_⟩
  calc
    latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        = latticeMass d (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) :=
          latticeMass_indep_cubicExhaustion Λ hf
    _ ≤ ENNReal.ofReal (-Real.log (Real.tanh (β * J))) :=
          latticeMass_le_neg_log_tanh_betaJ hd hJ hβ
    _ = ENNReal.ofReal
          (-Real.log (Real.tanh (β * J)) /
            cubicOriginPseudoMassFromParamsAtPair hα hr β J z) *
        ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) :=
          hmul.symm

end Ambient
end IsingModel
