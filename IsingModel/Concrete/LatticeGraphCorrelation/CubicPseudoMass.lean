import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassTanhProfile
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRate

/-!
# Cubic named-rate cluster and capstone wrappers

This capstone module contains anchored cubic named-rate cluster, summability,
product-sum, and bundled downstream APIs. Basic names live in
`CubicPseudoMassBasic`; tanh-profile bridges live in `CubicPseudoMassTanhProfile`;
named-rate lattice-mass and interval bridges live in `CubicPseudoMassNamedRate`.
-/

namespace IsingModel
namespace Ambient

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

end Ambient
end IsingModel
