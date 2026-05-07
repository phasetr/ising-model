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

/-- **Anchored cubic named-rate high-temperature comparison proposition**:
lightweight named proposition for the heavy comparison
`cubicOriginPseudoMassFromParamsAtPair ≤ -log(βJ·2d)`.

Keeping the comparison as an irreducible `Prop` avoids placing the full concrete
named-rate expression directly in downstream theorem conclusions, where direct
`cubicTanhProfileBound` wrappers trigger deterministic elaboration timeouts.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
@[irreducible] def cubicOriginNamedRateLeHighTemp {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (β J : ℝ) (z : Fin d → ℤ) : Prop :=
  cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
    -Real.log (β * J * ↑(2 * d))

/-- **Cubic truncated two-point product summand**: the product
`U₂(x,w) * U₂(y,w)` on the cubic exhaustion at zero external field.

This definition keeps downstream summability statements from repeatedly
unfolding the full cubic-exhaustion `truncated2Infinite` product. -/
noncomputable def cubicTruncated2Product (d : ℕ) (β J : ℝ)
    (x y w : Fin d → ℤ) : ℝ :=
  Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) x w *
    Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) y w

/-- **Anchored cubic tanh-power profile condition**: the lightweight named
predicate
`pseudoMassG α r (-log(βJ·2d)) ≤ tanh(βJ) ^ dist(0,z)`.

Keeping this condition named avoids repeatedly elaborating the tanh-profile
expression in downstream theorem statements. -/
def cubicTanhProfileBound (α d : ℕ) (r β J : ℝ) (z : Fin d → ℤ) : Prop :=
  pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
    Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z

/-- The named cubic tanh-power profile condition unfolds to the underlying
`pseudoMassG` lower-bound inequality. -/
theorem cubicTanhProfileBound_iff (α d : ℕ) (r β J : ℝ) (z : Fin d → ℤ) :
    cubicTanhProfileBound α d r β J z ↔
      pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
        Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z :=
  Iff.rfl

/-- **Cubic correlation lower bound from the named tanh-profile condition**:
the named predicate feeds the existing tanh-power bridge. -/
theorem cubicTanhProfileBound_le_cubic_correlation
    {α d : ℕ} {r β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : cubicTanhProfileBound α d r β J z) :
    pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} :=
  pseudoMassG_le_cubic_correlation_of_le_tanh_pow_dist
    (α := α) (d := d) (r := r) (β := β) (J := J)
    hJ hβ hz hprofile_tanh

/-- **Cubic pair-correlation positivity from the named tanh-profile condition**:
the named predicate supplies the existing tanh-profile positivity bridge. -/
theorem correlationInfinite_cubic_pair_pos_of_cubicTanhProfileBound
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : cubicTanhProfileBound α d r β J z) :
    0 < Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} :=
  correlationInfinite_cubic_pair_pos_of_pseudoMassG_le_tanh_pow_dist
    (α := α) hr hJ hβ hlt hz hprofile_tanh

/-- **Cubic pair active range from the named tanh-profile condition**:
the named predicate supplies the existing active-interval bridge. -/
theorem correlationInfinite_cubic_pair_mem_Ioo_zero_two_of_cubicTanhProfileBound
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : cubicTanhProfileBound α d r β J z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2 :=
  correlationInfinite_cubic_pair_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
    (α := α) hr hJ hβ hlt hz hprofile_tanh

/-- **Cubic pair correlation is nonzero from the named tanh-profile condition**:
positivity from the named predicate rules out zero. -/
theorem correlationInfinite_cubic_pair_ne_zero_of_cubicTanhProfileBound
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : cubicTanhProfileBound α d r β J z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} ≠ 0 :=
  correlationInfinite_cubic_pair_ne_zero_of_pseudoMassG_le_tanh_pow_dist
    (α := α) hr hJ hβ hlt hz hprofile_tanh

/-- **Cubic pair correlation is in `(0,1]` from the named tanh-profile
condition**: the named predicate supplies positivity and the existing universal
correlation bound supplies the upper endpoint. -/
theorem correlationInfinite_cubic_pair_mem_Ioc_zero_one_of_cubicTanhProfileBound
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : cubicTanhProfileBound α d r β J z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} ∈ Set.Ioc (0 : ℝ) 1 :=
  correlationInfinite_cubic_pair_mem_Ioc_zero_one_of_pseudoMassG_le_tanh_pow_dist
    (α := α) hr hJ hβ hlt hz hprofile_tanh

/-- **Cubic pair correlation is strictly below two from the named tanh-profile
condition**: this isolates the upper endpoint of the active interval package. -/
theorem correlationInfinite_cubic_pair_lt_two_of_cubicTanhProfileBound
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : cubicTanhProfileBound α d r β J z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} < 2 :=
  correlationInfinite_cubic_pair_lt_two_of_pseudoMassG_le_tanh_pow_dist
    (α := α) hr hJ hβ hlt hz hprofile_tanh

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

/-- **Target lattice-mass closed interval for an anchored cubic named rate**:
the nonnegative `ENNReal.ofReal` named rate lies in `[0, latticeMass]` once the
high-temperature rate comparison is available.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_ofReal_mem_Icc_latticeMass_of_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
      Set.Icc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨zero_le _,
    latticeMass_ge_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hr Λ hJ hβ hlt hle⟩

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

/-- **Target lattice-mass half-open interval for a positive anchored cubic
named rate**: positivity upgrades the closed interval membership to
`(0, latticeMass]`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_pos_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
      Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨ENNReal.ofReal_pos.mpr hpos,
    latticeMass_ge_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hr Λ hJ hβ hlt hle⟩

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

/-- **Named anchored cubic rate comparison from cubic profile inputs**:
active-range membership and the cubic profile lower bound prove the lightweight
named high-temperature comparison proposition.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicOriginNamedRateLeHighTemp_of_cubic_pseudoMassG_le_corr
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
    cubicOriginNamedRateLeHighTemp hα hr β J z := by
  rw [cubicOriginNamedRateLeHighTemp]
  exact cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubic_pseudoMassG_le_corr
    hα hr hJ hβ hlt hcorr_cubic hprofile_cubic

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

/-- The irreducible named comparison proposition unfolds to the underlying
high-temperature rate comparison when a downstream theorem needs the ordinary
inequality form. -/
theorem cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} {z : Fin d → ℤ}
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d)) := by
  rw [cubicOriginNamedRateLeHighTemp] at hnamed
  exact hnamed

/-- **Anchored cubic named proposition validates high-temperature decay**:
the lightweight named comparison proposition feeds the conditional decay
bridge without exposing the heavy comparison in the theorem statement.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_cubicOriginNamedRateLeHighTemp
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) :=
  HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
      hα hr hnamed)

/-- **Target lattice-mass lower bound from the named comparison proposition**:
the irreducible proposition form is enough to place the named rate below the
target-exhaustion `latticeMass`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_ge_cubicOriginPseudoMassFromParamsAtPair_of_cubicOriginNamedRateLeHighTemp
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ≤
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
      hα hr hnamed)

/-- **Closed target interval from the named comparison proposition**:
the `ENNReal.ofReal` named rate lies in `[0, latticeMass]` under the
irreducible comparison proposition.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_ofReal_mem_Icc_latticeMass_of_cubicOriginNamedRateLeHighTemp
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
      Set.Icc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  cubicNamedRate_ofReal_mem_Icc_latticeMass_of_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
      hα hr hnamed)

/-- **Positive target lattice mass from a positive named rate and named
comparison proposition**: strict positivity is supplied directly, and the
irreducible proposition supplies the high-temperature comparison.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_pos_of_cubicOriginNamedRateLeHighTemp_pos
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate
    hα hr Λ hJ hβ hlt hpos
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
      hα hr hnamed)

/-- **Half-open target interval from a positive named rate and named
comparison proposition**: direct positivity upgrades the named-proposition
closed interval to `(0, latticeMass]`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_cubicOriginNamedRateLeHighTemp_pos
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
      Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_pos_le_high_temp_rate
    hα hr Λ hJ hβ hlt hpos
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
      hα hr hnamed)

/-- **Nonzero target lattice mass from a positive named rate and named
comparison proposition**: the positive target lattice-mass bridge rules out
zero. -/
theorem latticeMass_ne_zero_of_cubicOriginNamedRateLeHighTemp_pos
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≠ 0 :=
  ne_of_gt
    (latticeMass_pos_of_cubicOriginNamedRateLeHighTemp_pos
      hα hr Λ hJ hβ hlt hpos hnamed)

/-- **Named-proposition decay plus half-open target interval from direct
positivity**: strict positivity supplies the interval lower endpoint while the
named proposition supplies decay and the upper endpoint.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_decay_mem_Ioc_of_cubicOriginNamedRateLeHighTemp_pos
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
        Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_cubicOriginNamedRateLeHighTemp
      hα hr Λ hJ hβ hlt hnamed,
    cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_cubicOriginNamedRateLeHighTemp_pos
      hα hr Λ hJ hβ hlt hpos hnamed⟩

/-- **Positive target lattice mass from active range plus named proposition**:
active-range membership supplies positivity of the named pseudo-mass, while the
irreducible proposition supplies the high-temperature comparison.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_pos_of_cubicOriginNamedRateLeHighTemp_cubic_corr_mem
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem hα hr hcorr_cubic)
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
      hα hr hnamed)

/-- **Half-open target interval from active range plus named proposition**:
the active-range proof gives the strict lower endpoint and the named proposition
gives the target lattice-mass upper endpoint.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_cubicOriginNamedRateLeHighTemp
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
      Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_pos_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem hα hr hcorr_cubic)
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
      hα hr hnamed)

/-- **Nonzero target lattice mass from active range plus named proposition**:
the positive target lattice-mass bridge also rules out zero. -/
theorem latticeMass_ne_zero_of_cubicOriginNamedRateLeHighTemp_cubic_corr_mem
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≠ 0 :=
  ne_of_gt
    (latticeMass_pos_of_cubicOriginNamedRateLeHighTemp_cubic_corr_mem
      hα hr Λ hJ hβ hlt hcorr_cubic hnamed)

/-- **Named-proposition decay plus closed target interval**: the irreducible
comparison proposition supplies both validating exponential decay and closed
interval membership for the named rate.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_decay_mem_Icc_of_cubicOriginNamedRateLeHighTemp
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
        Set.Icc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_cubicOriginNamedRateLeHighTemp
      hα hr Λ hJ hβ hlt hnamed,
    cubicNamedRate_ofReal_mem_Icc_latticeMass_of_cubicOriginNamedRateLeHighTemp
      hα hr Λ hJ hβ hlt hnamed⟩

/-- **Named-proposition decay plus half-open target interval**: active-range
membership upgrades the closed interval supplied by the named proposition to
the positive half-open interval.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_decay_mem_Ioc_of_cubicOriginNamedRateLeHighTemp
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
        Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_cubicOriginNamedRateLeHighTemp
      hα hr Λ hJ hβ hlt hnamed,
    cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_cubicOriginNamedRateLeHighTemp
      hα hr Λ hJ hβ hlt hcorr_cubic hnamed⟩

/-- **Cubic active-range/profile input bundle from the named tanh-profile
condition**: the named predicate supplies exactly the two hypotheses consumed by
the existing cubic profile-to-named-rate comparison bridge.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicTanhProfileBound_cubic_corr_mem_Ioo_and_profile
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : cubicTanhProfileBound α d r β J z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2 ∧
    pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} :=
  ⟨correlationInfinite_cubic_pair_mem_Ioo_zero_two_of_cubicTanhProfileBound
      hr hJ hβ hlt hz hprofile_tanh,
    cubicTanhProfileBound_le_cubic_correlation hJ hβ hz hprofile_tanh⟩

/-- **Eliminator for the named tanh-profile bridge inputs**: to prove an
arbitrary proposition `P`, it is enough to prove it from the active-range
membership and cubic profile lower bound supplied by `cubicTanhProfileBound`.

This avoids restating the tanh-power formula while keeping downstream proofs on
the stable cubic profile-to-named-rate bridge input layer.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicTanhProfileBound_elim_cubic_corr_mem_Ioo_and_profile
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : cubicTanhProfileBound α d r β J z) {P : Prop}
    (h :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2 →
      pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), z} →
      P) :
    P := by
  rcases cubicTanhProfileBound_cubic_corr_mem_Ioo_and_profile
      hr hJ hβ hlt hz hprofile_tanh with ⟨hcorr_cubic, hprofile_cubic⟩
  exact h hcorr_cubic hprofile_cubic

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

/-- **Target lattice-mass closed interval from a cubic profile lower bound**:
the cubic profile comparison places the `ENNReal.ofReal` named rate in
`[0, latticeMass]`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_ofReal_mem_Icc_latticeMass_of_cubic_pseudoMassG_le_corr
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
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
      Set.Icc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨zero_le _,
    latticeMass_ge_cubicOriginPseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
      hα hr Λ hJ hβ hlt hcorr_cubic hprofile_cubic⟩

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

/-- **Target lattice-mass half-open interval from a cubic profile lower bound**:
active-range membership and the profile comparison place the `ENNReal.ofReal`
named rate in `(0, latticeMass]`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_cubic_pseudoMassG_le_corr
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
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
      Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨ENNReal.ofReal_pos.mpr
      (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
        hα hr hcorr_cubic),
    latticeMass_ge_cubicOriginPseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
      hα hr Λ hJ hβ hlt hcorr_cubic hprofile_cubic⟩

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

/-- **Target lattice-mass half-open interval from cubic active range plus
named-rate comparison**: active-range membership supplies the strict lower
endpoint and the named-rate comparison supplies the target upper endpoint.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_corr_mem_le_high_temp_rate
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
    ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
      Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_pos_le_high_temp_rate
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem hα hr hcorr_cubic)
    hle

/-- **Named-rate decay plus closed target interval from high-temperature
comparison**: the conditional comparison supplies both validating exponential
decay and membership of `ENNReal.ofReal` of the named rate in
`[0, latticeMass]`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_decay_mem_Icc_of_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
        Set.Icc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hr Λ hJ hβ hlt hle,
    cubicNamedRate_ofReal_mem_Icc_latticeMass_of_le_high_temp_rate
      hα hr Λ hJ hβ hlt hle⟩

/-- **Named-rate decay plus half-open target interval from positivity and
high-temperature comparison**: positivity upgrades the interval component to
`(0, latticeMass]` while retaining the same validating decay proof.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_decay_mem_Ioc_of_pos_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
        Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hr Λ hJ hβ hlt hle,
    cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_pos_le_high_temp_rate
      hα hr Λ hJ hβ hlt hpos hle⟩

/-- **Named-rate decay plus closed target interval from a cubic profile lower
bound**: the active-range/profile inputs supply both the decay proof and
closed interval membership for the named anchored cubic rate.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_decay_mem_Icc_of_cubic_pseudoMassG_le_corr
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
        (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
        Set.Icc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
      hα hr Λ hJ hβ hlt hcorr_cubic hprofile_cubic,
    cubicNamedRate_ofReal_mem_Icc_latticeMass_of_cubic_pseudoMassG_le_corr
      hα hr Λ hJ hβ hlt hcorr_cubic hprofile_cubic⟩

/-- **Named-rate decay plus half-open target interval from a cubic profile
lower bound**: active-range membership upgrades the interval component to
`(0, latticeMass]`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_decay_mem_Ioc_of_cubic_pseudoMassG_le_corr
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
        (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
        Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
      hα hr Λ hJ hβ hlt hcorr_cubic hprofile_cubic,
    cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_cubic_pseudoMassG_le_corr
      hα hr Λ hJ hβ hlt hcorr_cubic hprofile_cubic⟩

/-- **Named-rate decay plus half-open target interval from active range and
high-temperature comparison**: active-range membership gives the strict lower
endpoint, and the named-rate comparison gives both decay and the upper endpoint.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_decay_mem_Ioc_of_corr_mem_le_high_temp_rate
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
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∈
        Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hr Λ hJ hβ hlt hle,
    cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_corr_mem_le_high_temp_rate
      hα hr Λ hJ hβ hlt hcorr_cubic hle⟩

/-- **Cluster property from a positive named cubic rate and high-temperature
comparison**: a positive named rate validating exponential decay gives the
target-exhaustion cluster property.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem clusterProperty_of_cubicNamedRate_pos_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) :
    clusterProperty (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  clusterProperty_latticeGraph_of_HasExponentialDecay d Λ
    (⟨J, 0, β⟩ : IsingParams ℝ) hpos
    (HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hr Λ hJ hβ hlt hle)

/-- **Cluster property from cubic active-range/profile inputs**: the cubic
profile bridge supplies a positive validating named rate.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem clusterProperty_of_cubicNamedRate_cubic_pseudoMassG_le_corr
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
    clusterProperty (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  clusterProperty_latticeGraph_of_HasExponentialDecay d Λ
    (⟨J, 0, β⟩ : IsingParams ℝ)
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
      hα hr hcorr_cubic)
    (HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
      hα hr Λ hJ hβ hlt hcorr_cubic hprofile_cubic)

/-- **Cluster property from cubic active range plus named-rate comparison**:
active-range membership supplies positivity and the comparison supplies decay.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem clusterProperty_of_cubicNamedRate_corr_mem_le_high_temp_rate
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
    clusterProperty (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  clusterProperty_of_cubicNamedRate_pos_le_high_temp_rate hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
      hα hr hcorr_cubic)
    hle

/-- **Cluster property from a positive named cubic rate and the named
comparison proposition**: the irreducible proposition supplies the comparison
input without restating the high-temperature inequality.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem clusterProperty_of_cubicOriginNamedRateLeHighTemp_pos
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    clusterProperty (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  clusterProperty_of_cubicNamedRate_pos_le_high_temp_rate hα hr Λ hJ hβ hlt
    hpos
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
      hα hr hnamed)

/-- **Cluster property from cubic active range and the named comparison
proposition**: active-range membership supplies positivity and the irreducible
proposition supplies the high-temperature comparison.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem clusterProperty_of_cubicOriginNamedRateLeHighTemp_cubic_corr_mem
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) :
    clusterProperty (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  clusterProperty_of_cubicOriginNamedRateLeHighTemp_pos hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
      hα hr hcorr_cubic)
    hnamed

/-- **Cubic product summability from a positive named cubic rate and
high-temperature comparison**: on the cubic exhaustion, the named rate feeds the
Step 127 product-summability theorem.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem summable_truncated2Infinite_prod_of_cubicNamedRate_pos_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) (x y : Fin d → ℤ) :
    Summable (cubicTruncated2Product d β J x y) := by
  simpa [cubicTruncated2Product] using
    (summable_truncated2Infinite_prod_of_hasExponentialDecay hJ hβ hpos
      (HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
        hα hr (Ambient.cubicExhaustion d) hJ hβ hlt hle)
      x y)

/-- **Cubic product summability from cubic active-range/profile inputs**:
the profile bridge supplies a positive named decay rate on the cubic exhaustion.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem summable_truncated2Infinite_prod_of_cubicNamedRate_cubic_pseudoMassG_le_corr
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
          {(0 : Fin d → ℤ), z}) (x y : Fin d → ℤ) :
    Summable (cubicTruncated2Product d β J x y) := by
  simpa [cubicTruncated2Product] using
    (summable_truncated2Infinite_prod_of_hasExponentialDecay hJ hβ
      (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
        hα hr hcorr_cubic)
      (HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_cubic_pseudoMassG_le_corr
        hα hr (Ambient.cubicExhaustion d) hJ hβ hlt hcorr_cubic hprofile_cubic)
      x y)

/-- **Cubic product summability from cubic active range plus named-rate
comparison**: active-range membership gives positivity and the comparison gives
the validating decay rate on the cubic exhaustion.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem summable_truncated2Infinite_prod_of_cubicNamedRate_corr_mem_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) (x y : Fin d → ℤ) :
    Summable (cubicTruncated2Product d β J x y) :=
  summable_truncated2Infinite_prod_of_cubicNamedRate_pos_le_high_temp_rate
    hα hr hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
      hα hr hcorr_cubic)
    hle x y

/-- **Cubic product summability from a positive named cubic rate and the named
comparison proposition**: the irreducible proposition supplies the validating
decay comparison on the cubic exhaustion.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem summable_truncated2Infinite_prod_of_cubicOriginNamedRateLeHighTemp_pos
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) (x y : Fin d → ℤ) :
    Summable (cubicTruncated2Product d β J x y) :=
  summable_truncated2Infinite_prod_of_cubicNamedRate_pos_le_high_temp_rate
    hα hr hJ hβ hlt hpos
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
      hα hr hnamed)
    x y

/-- **Cubic product summability from active range and the named comparison
proposition**: active-range membership supplies positivity and the irreducible
proposition supplies the comparison.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem summable_truncated2Infinite_prod_of_cubicOriginNamedRateLeHighTemp_cubic_corr_mem
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) (x y : Fin d → ℤ) :
    Summable (cubicTruncated2Product d β J x y) :=
  summable_truncated2Infinite_prod_of_cubicOriginNamedRateLeHighTemp_pos
    hα hr hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
      hα hr hcorr_cubic)
    hnamed x y

/-- **Cubic product-sum bound from a positive named cubic rate and
high-temperature comparison**: the named rate supplies an exponential-decay
witness, and Step 127 gives the explicit convolution bound with some witness
constant `C`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem exists_tsum_cubicTruncated2Product_le_of_cubicNamedRate_pos_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) (x y : Fin d → ℤ) :
    let m := cubicOriginPseudoMassFromParamsAtPair hα hr β J z
    ∃ C : ℝ, 0 ≤ C ∧
      ∑' w : Fin d → ℤ, cubicTruncated2Product d β J x y w ≤
        (C + 1) ^ 2 * (2 * ∑' w : Fin d → ℤ,
          Real.exp (-(m / 2) * (latticeDistance d 0 w : ℝ))) *
        Real.exp (-(m / 2) * (latticeDistance d x y : ℝ) / 2) := by
  dsimp
  obtain ⟨C, hC, hbound⟩ :=
    HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hr (Ambient.cubicExhaustion d) hJ hβ hlt hle
  refine ⟨C, hC, ?_⟩
  simpa [cubicTruncated2Product] using
    (tsum_truncated2Infinite_prod_le (d := d) (J := J) (β := β)
      (α := cubicOriginPseudoMassFromParamsAtPair hα hr β J z) (C := C)
      hJ hβ hpos hC hbound x y)

/-- **Cubic product-sum bound from cubic active-range/profile inputs**: the
cubic profile bridge supplies the positive named decay rate and the Step 127
convolution estimate supplies the bound.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem exists_tsum_cubicTruncated2Product_le_of_cubicNamedRate_cubic_pseudoMassG_le_corr
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
          {(0 : Fin d → ℤ), z}) (x y : Fin d → ℤ) :
    let m := cubicOriginPseudoMassFromParamsAtPair hα hr β J z
    ∃ C : ℝ, 0 ≤ C ∧
      ∑' w : Fin d → ℤ, cubicTruncated2Product d β J x y w ≤
        (C + 1) ^ 2 * (2 * ∑' w : Fin d → ℤ,
          Real.exp (-(m / 2) * (latticeDistance d 0 w : ℝ))) *
        Real.exp (-(m / 2) * (latticeDistance d x y : ℝ) / 2) :=
  exists_tsum_cubicTruncated2Product_le_of_cubicNamedRate_pos_le_high_temp_rate
    hα hr hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
      hα hr hcorr_cubic)
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubic_pseudoMassG_le_corr
      hα hr hJ hβ hlt hcorr_cubic hprofile_cubic)
    x y

/-- **Cubic product-sum bound from cubic active range plus named-rate
comparison**: active-range membership supplies positivity and the comparison
supplies the named exponential-decay rate.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem exists_tsum_cubicTruncated2Product_le_of_cubicNamedRate_corr_mem_le_high_temp_rate
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hle : cubicOriginPseudoMassFromParamsAtPair hα hr β J z ≤
      -Real.log (β * J * ↑(2 * d))) (x y : Fin d → ℤ) :
    let m := cubicOriginPseudoMassFromParamsAtPair hα hr β J z
    ∃ C : ℝ, 0 ≤ C ∧
      ∑' w : Fin d → ℤ, cubicTruncated2Product d β J x y w ≤
        (C + 1) ^ 2 * (2 * ∑' w : Fin d → ℤ,
          Real.exp (-(m / 2) * (latticeDistance d 0 w : ℝ))) *
        Real.exp (-(m / 2) * (latticeDistance d x y : ℝ) / 2) :=
  exists_tsum_cubicTruncated2Product_le_of_cubicNamedRate_pos_le_high_temp_rate
    hα hr hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
      hα hr hcorr_cubic)
    hle x y

/-- **Cubic product-sum bound from a positive named cubic rate and the named
comparison proposition**: the irreducible proposition supplies the validating
decay comparison and Step 127 supplies the explicit convolution bound.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem exists_tsum_cubicTruncated2Product_le_of_cubicOriginNamedRateLeHighTemp_pos
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) (x y : Fin d → ℤ) :
    let m := cubicOriginPseudoMassFromParamsAtPair hα hr β J z
    ∃ C : ℝ, 0 ≤ C ∧
      ∑' w : Fin d → ℤ, cubicTruncated2Product d β J x y w ≤
        (C + 1) ^ 2 * (2 * ∑' w : Fin d → ℤ,
          Real.exp (-(m / 2) * (latticeDistance d 0 w : ℝ))) *
        Real.exp (-(m / 2) * (latticeDistance d x y : ℝ) / 2) :=
  exists_tsum_cubicTruncated2Product_le_of_cubicNamedRate_pos_le_high_temp_rate
    hα hr hJ hβ hlt hpos
    (cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
      hα hr hnamed)
    x y

/-- **Cubic product-sum bound from active range and the named comparison
proposition**: active-range membership supplies positivity and the irreducible
proposition supplies the validating decay comparison.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem exists_tsum_cubicTruncated2Product_le_of_cubicOriginNamedRateLeHighTemp_cubic_corr_mem
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) (x y : Fin d → ℤ) :
    let m := cubicOriginPseudoMassFromParamsAtPair hα hr β J z
    ∃ C : ℝ, 0 ≤ C ∧
      ∑' w : Fin d → ℤ, cubicTruncated2Product d β J x y w ≤
        (C + 1) ^ 2 * (2 * ∑' w : Fin d → ℤ,
          Real.exp (-(m / 2) * (latticeDistance d 0 w : ℝ))) *
        Real.exp (-(m / 2) * (latticeDistance d x y : ℝ) / 2) :=
  exists_tsum_cubicTruncated2Product_le_of_cubicOriginNamedRateLeHighTemp_pos
    hα hr hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
      hα hr hcorr_cubic)
    hnamed x y

/-- **Capstone downstream bundle from a positive named cubic rate and the
named comparison proposition**: the irreducible proposition supplies the
high-temperature comparison input once, and strict positivity supplies the
positive interval, cluster, summability, and Step 127 product-sum consequences.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_capstone_bundle_of_cubicOriginNamedRateLeHighTemp_pos
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hpos : 0 < cubicOriginPseudoMassFromParamsAtPair hα hr β J z)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) (x y : Fin d → ℤ) :
    let m := cubicOriginPseudoMassFromParamsAtPair hα hr β J z
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) m ∧
      ENNReal.ofReal m ∈
        Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
      0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≠ 0 ∧
      clusterProperty (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      Summable (cubicTruncated2Product d β J x y) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∑' w : Fin d → ℤ, cubicTruncated2Product d β J x y w ≤
          (C + 1) ^ 2 * (2 * ∑' w : Fin d → ℤ,
            Real.exp (-(m / 2) * (latticeDistance d 0 w : ℝ))) *
          Real.exp (-(m / 2) * (latticeDistance d x y : ℝ) / 2) := by
  dsimp
  exact
    ⟨HasExponentialDecay_cubicOriginPseudoMassFromParamsAtPair_of_cubicOriginNamedRateLeHighTemp
        hα hr Λ hJ hβ hlt hnamed,
      cubicNamedRate_ofReal_mem_Ioc_latticeMass_of_cubicOriginNamedRateLeHighTemp_pos
        hα hr Λ hJ hβ hlt hpos hnamed,
      latticeMass_pos_of_cubicOriginNamedRateLeHighTemp_pos
        hα hr Λ hJ hβ hlt hpos hnamed,
      latticeMass_ne_zero_of_cubicOriginNamedRateLeHighTemp_pos
        hα hr Λ hJ hβ hlt hpos hnamed,
      clusterProperty_of_cubicOriginNamedRateLeHighTemp_pos
        hα hr Λ hJ hβ hlt hpos hnamed,
      summable_truncated2Infinite_prod_of_cubicOriginNamedRateLeHighTemp_pos
        hα hr hJ hβ hlt hpos hnamed x y,
      exists_tsum_cubicTruncated2Product_le_of_cubicOriginNamedRateLeHighTemp_pos
        hα hr hJ hβ hlt hpos hnamed x y⟩

/-- **Capstone downstream bundle from active range and the named comparison
proposition**: active-range membership supplies strict positivity, while the
irreducible proposition supplies the high-temperature comparison.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_capstone_bundle_of_cubicOriginNamedRateLeHighTemp_cubic_corr_mem
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hcorr_cubic : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z) (x y : Fin d → ℤ) :
    let m := cubicOriginPseudoMassFromParamsAtPair hα hr β J z
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) m ∧
      ENNReal.ofReal m ∈
        Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
      0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≠ 0 ∧
      clusterProperty (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      Summable (cubicTruncated2Product d β J x y) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∑' w : Fin d → ℤ, cubicTruncated2Product d β J x y w ≤
          (C + 1) ^ 2 * (2 * ∑' w : Fin d → ℤ,
            Real.exp (-(m / 2) * (latticeDistance d 0 w : ℝ))) *
          Real.exp (-(m / 2) * (latticeDistance d x y : ℝ) / 2) :=
  cubicNamedRate_capstone_bundle_of_cubicOriginNamedRateLeHighTemp_pos
    hα hr Λ hJ hβ hlt
    (cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem
      hα hr hcorr_cubic)
    hnamed x y

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

/-- **Capstone downstream bundle from cubic active-range/profile inputs**:
active-range membership supplies strict positivity, the profile lower bound
supplies the irreducible high-temperature comparison proposition, and the
bundle returns the target decay, interval, `latticeMass`, cluster, summability,
and Step 127 product-sum consequences.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_capstone_bundle_of_cubic_pseudoMassG_le_corr
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
          {(0 : Fin d → ℤ), z}) (x y : Fin d → ℤ) :
    let m := cubicOriginPseudoMassFromParamsAtPair hα hr β J z
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) m ∧
      ENNReal.ofReal m ∈
        Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
      0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≠ 0 ∧
      clusterProperty (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      Summable (cubicTruncated2Product d β J x y) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∑' w : Fin d → ℤ, cubicTruncated2Product d β J x y w ≤
          (C + 1) ^ 2 * (2 * ∑' w : Fin d → ℤ,
            Real.exp (-(m / 2) * (latticeDistance d 0 w : ℝ))) *
          Real.exp (-(m / 2) * (latticeDistance d x y : ℝ) / 2) :=
  cubicNamedRate_capstone_bundle_of_cubicOriginNamedRateLeHighTemp_cubic_corr_mem
    hα hr Λ hJ hβ hlt hcorr_cubic
    (cubicOriginNamedRateLeHighTemp_of_cubic_pseudoMassG_le_corr
      hα hr hJ hβ hlt hcorr_cubic hprofile_cubic)
    x y

/-- **Capstone downstream bundle from cubic active range plus raw comparison**:
active-range membership supplies strict positivity, while the explicit
high-temperature comparison is converted into the irreducible named proposition
before the bundle is applied.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_capstone_bundle_of_corr_mem_le_high_temp_rate
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
      -Real.log (β * J * ↑(2 * d))) (x y : Fin d → ℤ) :
    let m := cubicOriginPseudoMassFromParamsAtPair hα hr β J z
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) m ∧
      ENNReal.ofReal m ∈
        Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
      0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≠ 0 ∧
      clusterProperty (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      Summable (cubicTruncated2Product d β J x y) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∑' w : Fin d → ℤ, cubicTruncated2Product d β J x y w ≤
          (C + 1) ^ 2 * (2 * ∑' w : Fin d → ℤ,
            Real.exp (-(m / 2) * (latticeDistance d 0 w : ℝ))) *
          Real.exp (-(m / 2) * (latticeDistance d x y : ℝ) / 2) := by
  have hnamed : cubicOriginNamedRateLeHighTemp hα hr β J z := by
    rw [cubicOriginNamedRateLeHighTemp]
    exact hle
  exact
    cubicNamedRate_capstone_bundle_of_cubicOriginNamedRateLeHighTemp_cubic_corr_mem
      hα hr Λ hJ hβ hlt hcorr_cubic hnamed x y

/-- **Capstone downstream bundle from bundled cubic profile inputs**: a
single hypothesis supplies both anchored cubic active-range membership and the
cubic profile lower bound, then the active-range/profile capstone bundle returns
the target decay, interval, `latticeMass`, cluster, summability, and Step 127
product-sum consequences.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem cubicNamedRate_capstone_bundle_of_cubic_corr_mem_Ioo_and_profile
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
              {(0 : Fin d → ℤ), z}) (x y : Fin d → ℤ) :
    let m := cubicOriginPseudoMassFromParamsAtPair hα hr β J z
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) m ∧
      ENNReal.ofReal m ∈
        Set.Ioc 0 (latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
      0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≠ 0 ∧
      clusterProperty (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      Summable (cubicTruncated2Product d β J x y) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∑' w : Fin d → ℤ, cubicTruncated2Product d β J x y w ≤
          (C + 1) ^ 2 * (2 * ∑' w : Fin d → ℤ,
            Real.exp (-(m / 2) * (latticeDistance d 0 w : ℝ))) *
          Real.exp (-(m / 2) * (latticeDistance d x y : ℝ) / 2) := by
  rcases hinputs with ⟨hcorr_cubic, hprofile_cubic⟩
  exact cubicNamedRate_capstone_bundle_of_cubic_pseudoMassG_le_corr
    hα hr Λ hJ hβ hlt hcorr_cubic hprofile_cubic x y

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

/-- **High-temperature lattice-mass lower bound from the named cubic
tanh-profile predicate**: named input form of
`latticeMass_ge_neg_log_of_high_temp_exhaustion_of_cubic_tanh_profile`.

This keeps theorem statements on the lightweight `cubicTanhProfileBound`
predicate while avoiding the heavier concrete named-rate conclusion that still
triggers deterministic elaboration timeouts.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_ge_neg_log_of_high_temp_exhaustion_of_cubicTanhProfileBound
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : cubicTanhProfileBound α d r β J z) :
    ENNReal.ofReal (-Real.log (β * J * ↑(2 * d))) ≤
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_neg_log_of_high_temp_exhaustion_of_cubic_tanh_profile
    hr Λ hJ hβ hlt hz hprofile_tanh

/-- **Positive lattice mass from the named cubic tanh-profile predicate**:
named input form of
`latticeMass_pos_of_high_temp_exhaustion_of_cubic_tanh_profile`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_pos_of_high_temp_exhaustion_of_cubicTanhProfileBound
    {α d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ : 0 < β * J)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : cubicTanhProfileBound α d r β J z) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_high_temp_exhaustion_of_cubic_tanh_profile
    hd hr Λ hJ hβ hβJ hlt hz hprofile_tanh

/-- **High-temperature lattice-mass lower and positive bounds from the named
cubic tanh-profile predicate**: conjunction form for downstream Step 117l
arguments that need both final high-temperature lattice-mass consequences.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem latticeMass_ge_neg_log_and_pos_of_high_temp_exhaustion_of_cubicTanhProfileBound
    {α d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ : 0 < β * J)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : cubicTanhProfileBound α d r β J z) :
    ENNReal.ofReal (-Real.log (β * J * ↑(2 * d))) ≤
        latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  ⟨latticeMass_ge_neg_log_of_high_temp_exhaustion_of_cubicTanhProfileBound
      hr Λ hJ hβ hlt hz hprofile_tanh,
    latticeMass_pos_of_high_temp_exhaustion_of_cubicTanhProfileBound
      hd hr Λ hJ hβ hβJ hlt hz hprofile_tanh⟩

end Ambient
end IsingModel
