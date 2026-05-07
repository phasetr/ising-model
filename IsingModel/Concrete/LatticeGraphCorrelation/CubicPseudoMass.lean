import IsingModel.Concrete.LatticeGraphCorrelation.Inequalities

/-!
# Cubic tanh-profile lattice-mass corollaries

Small wrapper module for target-level high-temperature `latticeMass`
consequences under the anchored cubic tanh-profile hypotheses used in the
GJ §17.5 Lemma 17.5.2 bridge.
-/

namespace IsingModel
namespace Ambient

/-- **Anchored cubic pseudo-mass abbreviation**: the concrete
`pseudoMassFromParamsAtPair` value for the cubic exhaustion at the anchored
pair `(0,z)` and zero external field.

This definition is intended to keep downstream theorem statements from
restating the high-arity concrete pseudo-mass expression.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
noncomputable def cubicOriginPseudoMassFromParamsAtPair {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) : ℝ :=
  pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) 0 z

/-- The anchored cubic pseudo-mass abbreviation unfolds to the corresponding
`pseudoMassFromParamsAtPair` value. -/
theorem cubicOriginPseudoMassFromParamsAtPair_eq {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) :
    cubicOriginPseudoMassFromParamsAtPair hα hr β J z =
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 z :=
  rfl

/-- **Anchored cubic pseudo-mass nonnegativity**. -/
theorem cubicOriginPseudoMassFromParamsAtPair_nonneg {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) :
    0 ≤ cubicOriginPseudoMassFromParamsAtPair hα hr β J z := by
  rw [cubicOriginPseudoMassFromParamsAtPair_eq]
  exact pseudoMassFromParamsAtPair_nonneg hα hr d (Ambient.cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) 0 z

/-- Transport a `≤` comparison between the named anchored cubic pseudo-mass and
the underlying concrete `pseudoMassFromParamsAtPair` expression. -/
theorem cubicOriginPseudoMassFromParamsAtPair_le_iff {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) (t : ℝ) :
    cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤ t ↔
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 z ≤ t := by
  rw [cubicOriginPseudoMassFromParamsAtPair_eq]

/-- Transport a `<` comparison between the named anchored cubic pseudo-mass and
the underlying concrete `pseudoMassFromParamsAtPair` expression. -/
theorem cubicOriginPseudoMassFromParamsAtPair_lt_iff {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) (t : ℝ) :
    cubicOriginPseudoMassFromParamsAtPair hα hr β J z < t ↔
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 z < t := by
  rw [cubicOriginPseudoMassFromParamsAtPair_eq]

/-- Transport equality between the named anchored cubic pseudo-mass and the
underlying concrete `pseudoMassFromParamsAtPair` expression. -/
theorem cubicOriginPseudoMassFromParamsAtPair_eq_iff {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) (t : ℝ) :
    cubicOriginPseudoMassFromParamsAtPair hα hr β J z = t ↔
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 z = t := by
  rw [cubicOriginPseudoMassFromParamsAtPair_eq]

/-- Transport a `≥` comparison between the named anchored cubic pseudo-mass and
the underlying concrete `pseudoMassFromParamsAtPair` expression. -/
theorem cubicOriginPseudoMassFromParamsAtPair_ge_iff {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) (t : ℝ) :
    t ≤ cubicOriginPseudoMassFromParamsAtPair hα hr β J z ↔
      t ≤ pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 z := by
  rw [cubicOriginPseudoMassFromParamsAtPair_eq]

/-- Transport a `>` comparison between the named anchored cubic pseudo-mass and
the underlying concrete `pseudoMassFromParamsAtPair` expression. -/
theorem cubicOriginPseudoMassFromParamsAtPair_gt_iff {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) (t : ℝ) :
    t < cubicOriginPseudoMassFromParamsAtPair hα hr β J z ↔
      t < pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 z := by
  rw [cubicOriginPseudoMassFromParamsAtPair_eq]

/-- Transport non-equality between the named anchored cubic pseudo-mass and the
underlying concrete `pseudoMassFromParamsAtPair` expression. -/
theorem cubicOriginPseudoMassFromParamsAtPair_ne_iff {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) (t : ℝ) :
    cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≠ t ↔
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 z ≠ t := by
  rw [cubicOriginPseudoMassFromParamsAtPair_eq]

/-- **Anchored cubic pseudo-mass validates high-temperature decay**:
if the named anchored cubic pseudo-mass is bounded above by the transferred
high-temperature rate, then it is a valid exponential-decay rate for any target
exhaustion.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) :=
  HasExponentialDecay_mono d Λ (⟨J, 0, β⟩ : IsingParams ℝ) hle
    (HasExponentialDecay_transfer_high_temp Λ hJ hβ hlt)

/-- **Anchored cubic pseudo-mass lower bound on target lattice mass**:
under the high-temperature comparison for the named anchored cubic pseudo-mass,
that pseudo-mass is bounded above by the target-exhaustion `latticeMass`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_ge_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ≤
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_of_HasExponentialDecay
    (cubicOriginPseudoMassFromParamsAtPair_nonneg hα hr β J z)
    (HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hr Λ hJ hβ hlt hle)

/-- **Positive target lattice mass from a positive anchored cubic pseudo-mass**:
if the named anchored cubic pseudo-mass is positive and no larger than the
high-temperature rate, then the target-exhaustion `latticeMass` is positive.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_HasExponentialDecay hpos
    (HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hr Λ hJ hβ hlt hle)

/-- **Nonzero target lattice mass from a positive anchored cubic pseudo-mass**:
the positive lattice-mass bridge also rules out zero. -/
theorem latticeMass_ne_zero_of_cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≠ 0 :=
  ne_of_gt
    (latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate
      hα hr Λ hJ hβ hlt hpos hle)

/-- **Anchored cubic named-rate comparison from a cubic profile lower bound**:
if the anchored cubic pair correlation lies in the active pseudo-mass interval
and dominates `pseudoMassG` at the transferred high-temperature rate, then the
named anchored cubic pseudo-mass is no larger than that rate.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z}) :
    cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d)) := by
  exact (cubicOriginPseudoMassFromParamsAtPair_le_iff hα hr β J z
      (-Real.log (β * J * ↑(2 * d)))).2
    (pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hr (Ambient.cubicExhaustion d) hJ hβ hlt hcorr_cubic hprofile_cubic)

/-- **Anchored cubic named pseudo-mass is positive from cubic active range**:
active-range membership of the anchored cubic pair correlation gives strict
positivity of the named concrete pseudo-mass.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2) :
    0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z := by
  rw [cubicOriginPseudoMassFromParamsAtPair_eq]
  exact pseudoMassFromParamsAtPair_pos_of_corr_mem hα hr d
    (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) 0 z hcorr_cubic

/-- **Anchored cubic named rate validates high-temperature decay from a cubic
profile lower bound**: the named-rate comparison supplied by the cubic profile
input feeds the conditional named-rate bridge.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z}) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) :=
  HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubic_pseudoMassG_le_corr
      hα hr hJ hβ hlt hcorr_cubic hprofile_cubic)

/-- **Anchored cubic named pseudo-mass lower bound from a cubic profile lower
bound**: under the profile condition, the named anchored cubic pseudo-mass is
bounded above by the target-exhaustion `latticeMass`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_ge_cubicOriginPseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z}) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ≤
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubic_pseudoMassG_le_corr
      hα hr hJ hβ hlt hcorr_cubic hprofile_cubic)

/-- **Positive target lattice mass from a positive anchored cubic named rate
generated by a cubic profile lower bound**: the active-range and profile
conditions supply both positivity of the named pseudo-mass and its comparison
with the high-temperature rate.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z}) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
      hα hr hcorr_cubic)
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubic_pseudoMassG_le_corr
      hα hr hJ hβ hlt hcorr_cubic hprofile_cubic)

/-- **Nonzero target lattice mass from a cubic profile lower bound**:
the active-range and profile inputs imply positive target `latticeMass`, hence
non-vanishing. -/
theorem latticeMass_ne_zero_of_cubicOriginPseudoMassFromParamsAtPair_cubic_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile_cubic : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z}) :
    latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≠ 0 :=
  ne_of_gt
    (latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_cubic_pseudoMassG_le_corr
      hα hr Λ hJ hβ hlt hcorr_cubic hprofile_cubic)

/-- **Anchored cubic named pseudo-mass nonzero from cubic active range**:
strict positivity from active-range membership rules out zero.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicOriginPseudoMassFromParamsAtPair_ne_zero_of_cubic_corr_mem
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2) :
    cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≠ 0 :=
  ne_of_gt (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
    hα hr hcorr_cubic)

/-- **Positive `ENNReal.ofReal` named rate from cubic active range**:
active-range membership makes the named anchored cubic pseudo-mass strictly
positive after coercion to `ENNReal`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem ENNReal_ofReal_cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2) :
    0 < ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) :=
  ENNReal.ofReal_pos.mpr
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
      hα hr hcorr_cubic)

/-- **Nonzero `ENNReal.ofReal` named rate from cubic active range**:
the positive coercion supplied by active-range membership is nonzero. -/
theorem ENNReal_ofReal_cubicOriginPseudoMassFromParamsAtPair_ne_zero_of_cubic_corr_mem
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ≠ 0 :=
  ne_of_gt
    (ENNReal_ofReal_cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
      hα hr hcorr_cubic)

/-- **Positive target lattice mass from cubic active range plus named-rate
comparison**: active-range membership supplies positivity of the named
pseudo-mass, so it is enough to prove the high-temperature rate comparison.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_cubic_corr_mem_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem hα hr hcorr_cubic)
    hle

/-- **Nonzero target lattice mass from cubic active range plus named-rate
comparison**: the positive target `latticeMass` bridge rules out zero. -/
theorem latticeMass_ne_zero_of_cubic_corr_mem_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≠ 0 :=
  ne_of_gt
    (latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_cubic_corr_mem_le_high_temp_rate
      hα hr Λ hJ hβ hlt hcorr_cubic hle)

/-- **High-temperature lattice-mass lower bound under a cubic tanh-profile
hypothesis**: this checks the anchored cubic active-range theorem generated by
the same tanh-profile hypothesis and then returns the transferred Simon--Lieb
high-temperature lower bound.

The lower-bound conclusion is the existing high-temperature estimate; the
active-range proof is not part of the returned theorem.  The profile hypothesis
is retained as a compatibility condition while the direct concrete
`pseudoMassFromParamsAtPair` wrapper remains too expensive to expose in a new
theorem conclusion.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_ge_neg_log_of_high_temp_exhaustion_of_cubic_tanh_profile
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    ENNReal.ofReal (-Real.log (β * J * ↑(2 * d))) ≤
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  have _hactive :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationInfinite_cubic_pair_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
      (α := α) hr hJ hβ hlt hz hprofile_tanh
  exact latticeMass_ge_neg_log_of_high_temp_exhaustion Λ hJ hβ hlt

/-- **Positive lattice mass under a cubic tanh-profile hypothesis**: checks the
profile-compatible active-range theorem internally and then applies the
transferred high-temperature positive-mass theorem.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_pos_of_high_temp_exhaustion_of_cubic_tanh_profile
    {α d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ : 0 < β * J)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  have _hactive :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationInfinite_cubic_pair_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
      (α := α) hr hJ hβ hlt hz hprofile_tanh
  exact latticeMass_pos_of_high_temp_exhaustion hd Λ hJ hβ hβJ hlt

end Ambient
end IsingModel
