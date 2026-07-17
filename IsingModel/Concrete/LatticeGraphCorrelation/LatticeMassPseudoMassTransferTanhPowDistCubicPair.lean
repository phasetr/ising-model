import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeCorrelationInequalities
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationSymmetry
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagTwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferTanhPowDist
import IsingModel.PseudoMass

/-!
# Lattice-mass cubic pair correlation tanh-power profile wrappers

Narrow child module for four ℤ^d cubic-pair correlation wrappers extracted
from `LatticeMassPseudoMassTransferTanhPowDist.lean`:
`correlationInfinite_cubic_pair_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist`,
`correlationInfinite_cubic_pair_ne_zero_of_pseudoMassG_le_tanh_pow_dist`,
`correlationInfinite_cubic_pair_mem_Ioc_zero_one_of_pseudoMassG_le_tanh_pow_dist`,
`correlationInfinite_cubic_pair_lt_two_of_pseudoMassG_le_tanh_pow_dist`.

Each wrapper is a thin pass-through to the anchored cubic-pair positivity
bridge and the universal correlation bound.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Cubic pair active range from a tanh-power profile bound**:
the tanh-power reduction supplies a positive lower bound on the anchored cubic
pair correlation, and the universal correlation bound gives the upper endpoint
`< 2`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem correlationInfinite_cubic_pair_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2 := by
  constructor
  · exact correlationInfinite_cubic_pair_pos_of_pseudoMassG_le_tanh_pow_dist
      hr hJ hβ hlt hz hprofile_tanh
  · exact lt_of_le_of_lt
      (Ambient.correlationInfinite_le_one (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({(0 : Fin d → ℤ), z} : Finset (Fin d → ℤ)))
      one_lt_two

/-- **Cubic pair correlation is nonzero from a tanh-power profile bound**:
positivity of the anchored cubic pair correlation rules out zero.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem correlationInfinite_cubic_pair_ne_zero_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} ≠ 0 :=
  ne_of_gt
    (correlationInfinite_cubic_pair_pos_of_pseudoMassG_le_tanh_pow_dist
      hr hJ hβ hlt hz hprofile_tanh)

/-- **Cubic pair correlation is in `(0,1]` from a tanh-power profile bound**:
the tanh-power hypothesis gives positivity, while boundedness of correlations
gives the endpoint `≤ 1`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem correlationInfinite_cubic_pair_mem_Ioc_zero_one_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} ∈ Set.Ioc (0 : ℝ) 1 := by
  constructor
  · exact correlationInfinite_cubic_pair_pos_of_pseudoMassG_le_tanh_pow_dist
      hr hJ hβ hlt hz hprofile_tanh
  · exact Ambient.correlationInfinite_le_one (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ({(0 : Fin d → ℤ), z} : Finset (Fin d → ℤ))

/-- **Cubic pair correlation is strictly below two from a tanh-power profile
bound**: this is the upper endpoint of the active interval package.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem correlationInfinite_cubic_pair_lt_two_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {(0 : Fin d → ℤ), z} < 2 :=
  (correlationInfinite_cubic_pair_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
    (α := α) hr hJ hβ hlt hz hprofile_tanh).2

end Ambient
end IsingModel
