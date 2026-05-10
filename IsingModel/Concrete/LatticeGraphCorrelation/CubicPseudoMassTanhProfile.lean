import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransfer

/-!
# Cubic tanh-profile bridges

This module contains named tanh-profile bridge theorems for the anchored cubic
pseudo-mass API. It sits between the lightweight names in `CubicPseudoMassBasic`
and the larger `CubicPseudoMass` capstone module.
-/

namespace IsingModel
namespace Ambient

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
