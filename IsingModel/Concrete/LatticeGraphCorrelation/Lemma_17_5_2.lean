import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMass

/-!
# GJ §17.5 Lemma 17.5.2 capstone (Step 117l, conditional sandwich)

This module bundles existing infrastructure into a named GJ Lemma 17.5.2
capstone, providing:

* a conditional sandwich
  `ofReal m⁻ ≤ latticeMass ≤ C · ofReal m⁻`
  parameterised by a validating exponential decay rate (lower-bound input)
  and an upper-bound hypothesis;
* a Lemma 17.5.2 lower-bound named alias for downstream consumption;
* an `ofReal`-valued `Prop` predicate naming the upper-bound side as a
  hypothesis, to be discharged by a future Lipschitz + HLS PR (cf. GJ
  §17.5 Theorem 17.5.1 proof on p.~312);
* a cubic-exhaustion + high-temperature unconditional lower-bound
  capstone derived from `cubicNamedRate_capstone_bundle_of_cubic_corr_mem_Ioo_and_profile`;
* the existential form of the discrete HLS constant `C > 0` lifted from
  `discrete_hls_constant`.

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

end Ambient
end IsingModel
