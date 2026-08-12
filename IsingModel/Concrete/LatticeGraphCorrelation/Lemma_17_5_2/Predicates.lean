import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMass
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempLipschitz
import IsingModel.PolyDecay

/-!
# GJ §17.5 Lemma 17.5.2 capstone — predicates and conditional sandwiches

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2` development. It
collects the upper-bound `Prop` predicate naming the substantive missing
inequality from GJ Lemma 17.5.2, the lower-bound named alias, the
order-theoretic upper-bound assembly from a uniform bound on every validating
decay rate, and the conditional sandwich capstones combining the two sides.

Tracking issue: <https://github.com/phasetr/ising-model/issues/1645>.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2,
  pp.~311--312.
* B. Simon, *Correlation inequalities and the decay of correlations in
  ferromagnets*, Comm. Math. Phys. 77 (1980), 111--126.
* E. H. Lieb, *A refinement of Simon's correlation inequality*, Comm. Math.
  Phys. 77 (1980), 127--135.
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

/-- **GJ §17.5 Lemma 17.5.2 upper-bound assembly from all decay rates**:
because `latticeMass` is the `sSup` of all validating nonnegative exponential
decay rates, the upper-bound predicate follows once every admissible rate
`a : NNReal` is bounded by `C · ofReal m⁻`.

This is the order-theoretic final step of the HLS upper-bound side.  The
analytic work still lies in proving the hypothesis, typically from the
infinite-volume HLS denominator comparison and the Lipschitz machinery.

References: Glimm--Jaffe §17.5, Lemma 17.5.2 and Theorem 17.5.1 proof,
pp.~311--312. -/
theorem lemma_17_5_2_upper_bound_of_all_decay_rates_le
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ) (C : ENNReal)
    (hdecay_le : ∀ a : NNReal,
      HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) →
        (a : ENNReal) ≤
          C * ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z)) :
    Lemma_17_5_2_UpperBound hα hr Λ J β x z C := by
  dsimp [Lemma_17_5_2_UpperBound, latticeMass]
  apply sSup_le
  rintro b ⟨a, ha, rfl⟩
  exact hdecay_le a ha

/-- **GJ §17.5 Lemma 17.5.2 upper-bound equivalence**: the named upper-bound
predicate is equivalent to bounding every validating nonnegative exponential
decay rate by `C · ofReal m⁻`.

This exposes the exact target shape needed by the future HLS argument: prove
the all-rate estimate, and the `latticeMass` upper-bound side follows by the
`sSup` definition; conversely, any closed upper-bound predicate immediately
controls every admissible decay rate. -/
theorem lemma_17_5_2_upper_bound_iff_all_decay_rates_le
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ) (C : ENNReal) :
    Lemma_17_5_2_UpperBound hα hr Λ J β x z C ↔
      ∀ a : NNReal,
        HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) →
          (a : ENNReal) ≤
            C * ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  constructor
  · intro hupper a hdecay
    have ha_mass :
        (a : ENNReal) ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
      simpa [ENNReal.ofReal_coe_nnreal] using
        latticeMass_ge_of_HasExponentialDecay (show 0 ≤ (a : ℝ) from a.2) hdecay
    exact ha_mass.trans hupper
  · intro hdecay_le
    exact lemma_17_5_2_upper_bound_of_all_decay_rates_le
      hα hr Λ J β x z C hdecay_le

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

/-- **GJ §17.5 Lemma 17.5.2 sandwich from lower decay and all-rate upper
assembly**: a validating pseudo-mass decay rate gives the lower bound, while a
uniform bound on every validating decay rate by `C · ofReal m⁻` gives the named
upper-bound side by `sSup_le`.

This theorem packages the final non-analytic assembly shape for the future HLS
upper-bound proof: downstream work only has to prove the all-decay-rate bound.

References: Glimm--Jaffe §17.5, Lemma 17.5.2 and Theorem 17.5.1 proof,
pp.~311--312. -/
theorem lemma_17_5_2_sandwich_of_decay_and_all_decay_rates_le
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} {x z : Fin d → ℤ} {C : ENNReal}
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z))
    (hdecay_le : ∀ a : NNReal,
      HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) →
        (a : ENNReal) ≤
          C * ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z)) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
      C * ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_sandwich_of_decay_and_upper hα hr hdecay
    (lemma_17_5_2_upper_bound_of_all_decay_rates_le hα hr Λ J β x z C hdecay_le)

end Ambient
end IsingModel
