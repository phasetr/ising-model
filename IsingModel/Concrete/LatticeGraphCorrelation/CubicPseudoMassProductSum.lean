import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRate

/-!
# Cubic named-rate product-sum wrappers

This module contains anchored cubic named-rate product-sum wrappers. It builds
on the cluster and product-summability layer in
`CubicPseudoMassClusterSummability` and feeds the larger `CubicPseudoMass`
capstone module.
-/

namespace IsingModel
namespace Ambient

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

end Ambient
end IsingModel
