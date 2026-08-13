import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassClusterSummability

/-!
# Summability of the cubic truncated two-point product

Records that `w ↦ U₂(x, w) · U₂(y, w)`, the product of infinite-volume Ursell two-point
functions on the cubic exhaustion at zero external field, is summable over ℤ^d at arbitrary
basepoints `x` and `y`, whenever the origin-anchored cubic pseudo-mass is strictly positive
and bounded above by the high-temperature rate `-log(βJ·2d)`. Every statement assumes
`0 ≤ J`, `0 < β` and `βJ·2d < 1`. Positivity is either hypothesised outright or read off the
anchored cubic pair correlation lying in `(0,2)`; the comparison is either hypothesised,
packaged in the irreducible `cubicOriginNamedRateLeHighTemp`, or obtained from a
`pseudoMassG` lower bound on that same correlation.

Reference: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312.
-/

namespace IsingModel
namespace Ambient

/-- **Cubic product summability from a positive named cubic rate and
high-temperature comparison**: on the cubic exhaustion, the named rate feeds the
Step 127 product-summability theorem.

Reference: Glimm--Jaffe §17.1 pp. 304--306 and §17.5 Lemma 17.5.2 pp. 311--312. -/
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

Reference: Glimm--Jaffe §17.1 pp. 304--306 and §17.5 Lemma 17.5.2 pp. 311--312. -/
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

Reference: Glimm--Jaffe §17.1 pp. 304--306 and §17.5 Lemma 17.5.2 pp. 311--312. -/
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

Reference: Glimm--Jaffe §17.1 pp. 304--306 and §17.5 Lemma 17.5.2 pp. 311--312. -/
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

Reference: Glimm--Jaffe §17.1 pp. 304--306 and §17.5 Lemma 17.5.2 pp. 311--312. -/
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

end Ambient
end IsingModel
