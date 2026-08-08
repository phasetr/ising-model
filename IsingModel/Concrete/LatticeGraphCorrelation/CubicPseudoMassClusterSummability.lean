import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRate
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRateCorr

/-!
# Cluster property from the origin-anchored cubic pseudo-mass

Derives the cluster property of the infinite-volume Ursell two-point function on ℤ^d — decay
to zero along the cofinite filter at every basepoint — at an arbitrary target exhaustion,
from a strictly positive origin-anchored cubic pseudo-mass bounded above by the
high-temperature rate `-log(βJ·2d)`: such a pseudo-mass is a validating exponential-decay
rate, and a positive rate forces the cofinite limit. Every statement assumes `0 ≤ J`,
`0 < β` and `βJ·2d < 1`. Positivity is either hypothesised outright or read off the anchored
cubic pair correlation lying in `(0,2)`; the comparison is either hypothesised, packaged in
the irreducible `cubicOriginNamedRateLeHighTemp`, or obtained from a `pseudoMassG` lower
bound on that same correlation.
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

end Ambient
end IsingModel
