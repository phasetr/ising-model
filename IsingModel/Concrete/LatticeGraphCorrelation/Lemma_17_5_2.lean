import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMass
import IsingModel.PolyDecay

/-!
# GJ §17.5 Lemma 17.5.2 capstone (Step 117l)

This module bundles existing infrastructure into a named GJ Lemma 17.5.2
capstone, providing:

* a conditional sandwich
  `ofReal m⁻ ≤ latticeMass ≤ C · ofReal m⁻`
  parameterised by a validating exponential decay rate (lower-bound input)
  and an upper-bound hypothesis;
* a Lemma 17.5.2 lower-bound named alias for downstream consumption;
* an `ofReal`-valued `Prop` predicate naming the upper-bound side as a
  hypothesis. In the cubic active-range high-temperature setting this module
  discharges the predicate with the finite Step 115 constant
  `-log(tanh(βJ)) / m⁻`; the sharper HLS-uniform constant remains future work
  (cf. GJ §17.5 Theorem 17.5.1 proof on p.~312);
* a cubic-exhaustion + high-temperature unconditional lower-bound
  capstone derived from `cubicNamedRate_capstone_bundle_of_cubic_corr_mem_Ioo_and_profile`;
* a finite cubic high-temperature sandwich capstone combining the lower-bound
  capstone with the finite Step 115 upper bridge;
* the existential form of the discrete HLS constant `C > 0` lifted from
  `discrete_hls_constant`;
* the uniform discrete HLS convolution constant packaged under the Lemma 17.5.2
  namespace for the future Lipschitz/HLS upper-bound composition.

Tracking issue: <https://github.com/phasetr/ising-model/issues/1645>.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2,
  pp.~311--312.
* Friedli--Velenik, §9, Prop. 9.31 (Simon--Lieb).
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 upper-bound predicate (hypothesis form)**:
the `Prop` `latticeMass d Λ p ≤ C · ENNReal.ofReal (pseudoMassFromParamsAtPair …)`
named so that the conditional capstone can take it explicitly. This is the
side of Lemma 17.5.2 that requires the Lipschitz capstone
(`pseudoMass_pow_succ_lipschitz`, Step 134) combined with the discrete HLS
integration; it is currently kept as a hypothesis pending a future
unconditional proof.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, p.~311--312. -/
def Lemma_17_5_2_UpperBound {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ) (C : ENNReal) : Prop :=
  latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
    C * ENNReal.ofReal
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z)

/-- **GJ §17.5 Lemma 17.5.2 lower-bound side (named alias)**: if the concrete
pseudo-mass associated to the pair `(x, z)` at `h = 0` validates exponential
decay of `truncated2Infinite`, then `ENNReal.ofReal m⁻ ≤ latticeMass`.

This is a renaming of `latticeMass_ge_pseudoMassFromParamsAtPair_of_decay`
under the Lemma 17.5.2 banner so that the capstone API uses GJ-named
identifiers rather than infrastructure-named identifiers.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, p.~311--312. -/
theorem lemma_17_5_2_lower_bound_of_decay
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} {x z : Fin d → ℤ}
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z)) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_pseudoMassFromParamsAtPair_of_decay hα hr hdecay

/-- **GJ §17.5 Lemma 17.5.2 conditional sandwich capstone**: given
(i) a validating exponential decay rate `HasExponentialDecay d Λ p m⁻`
discharging the lower-bound side, and
(ii) the explicit upper-bound hypothesis
`latticeMass ≤ C · ENNReal.ofReal m⁻`,
the canonical Lemma 17.5.2 sandwich
  `ENNReal.ofReal m⁻ ≤ latticeMass ≤ C · ENNReal.ofReal m⁻`
holds, where `m⁻ := pseudoMassFromParamsAtPair`.

This is the named capstone interface for GJ Lemma 17.5.2. The upper-bound
hypothesis names the substantive missing piece (cf.
`Lemma_17_5_2_UpperBound`); the lower bound is automatic from the
exponential-decay infrastructure.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, p.~311--312. -/
theorem lemma_17_5_2_sandwich_of_decay_and_upper
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} {x z : Fin d → ℤ}
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z))
    {C : ENNReal}
    (hupper : Lemma_17_5_2_UpperBound hα hr Λ J β x z C) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
      C * ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  ⟨lemma_17_5_2_lower_bound_of_decay hα hr hdecay, hupper⟩

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

References: Glimm--Jaffe §17.5, pp.~304--306 and Lemma 17.5.2,
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

/-- **GJ §17.5 Lemma 17.5.2 constant existence (alias of
`discrete_hls_constant`)**: under `2α > d` the discrete Hardy--Littlewood--Sobolev
constant exists. This is the existence side of the constant `C > 0` appearing
in the Lemma 17.5.2 upper-bound side `m ≤ C · m⁻`.

The actual quantitative bound matching the GJ Lipschitz argument (Theorem
17.5.1 proof, p.~312) is a future PR; this lemma exposes the existence of a
positive constant under the HLS hypothesis so that downstream statements can
quote `C` without re-stating its existence proof.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
theorem lemma_17_5_2_constant_existence (α d : ℕ) (hαd : 2 * α > d) :
    ∃ C : ℝ, 0 < C :=
  discrete_hls_constant α d hαd

/-- **GJ §17.5 Lemma 17.5.2 HLS convolution constant**: under `2α > d`
there is a positive constant uniformly bounding the polynomial convolution
kernel
`∑_w (1 + dist x w)^(-α) * (1 + dist y w)^(-α)`.

This is the constant-form HLS input used in the upper-bound/Lipschitz side of
Lemma 17.5.2. It is stronger than the bare existence alias
`lemma_17_5_2_constant_existence`, because the returned constant carries the
actual convolution inequality needed downstream.

References: Glimm--Jaffe §17.5, Lemma 17.5.2 and Theorem 17.5.1 proof,
pp.~311--312. -/
theorem lemma_17_5_2_hls_convolution_constant (α d : ℕ) (hαd : 2 * α > d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y w : ℝ) ^ (-(α : ℝ)) ≤ C :=
  IsingModel.discrete_hls_convolution_constant α d hαd

end Ambient
end IsingModel
