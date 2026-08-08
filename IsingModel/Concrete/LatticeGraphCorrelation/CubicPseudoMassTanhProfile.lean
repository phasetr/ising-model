import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferTanhPowDistCubicPair
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassTanhProfileCubicPair

/-!
# From the named tanh-power profile condition to the cubic-correlation inputs

Converts `cubicTanhProfileBound`, the named condition
`pseudoMassG α r (-log(βJ·2d)) ≤ tanh(βJ) ^ dist(0, z)`, into the hypotheses that the
profile-to-rate comparison consumes: the anchored cubic pair correlation dominates the
profile value `pseudoMassG α r (-log(βJ·2d))`, it is strictly positive and lies in `(0,2)`,
and an eliminator feeds those facts to an arbitrary goal. Domination transfers along the
tanh-power lower bound on that correlation and assumes only `0 ≤ J`, `0 < β` and a nonzero
displacement; positivity, the `(0,2)` placement and the eliminator additionally assume
`0 < r` and `βJ·2d < 1`.
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

end Ambient
end IsingModel
