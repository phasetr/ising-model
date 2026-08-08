import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferTanhPowDistCubicPair

/-!
# The anchored cubic pair correlation under the named tanh-power profile condition

Locates the ℤ^d infinite-volume pair correlation at `(0, z)` on the cubic exhaustion at zero
external field, once `cubicTanhProfileBound` holds: it is strictly positive, hence nonzero,
and it lies in `(0,1]` and in `(0,2)`. The lower endpoint is what the profile condition
buys, through the tanh-power lower bound on that correlation; the upper endpoints come from
the unconditional bound `correlationInfinite ≤ 1`, so the correlation lies below `2` even
without the profile condition. The isolated `< 2` statement nevertheless keeps that
condition, and proves its bound by projecting the profile-conditioned active-range
membership rather than by applying the unconditional bound directly. Every statement assumes
`0 < r`, `0 ≤ J`, `0 < β`, `βJ·2d < 1` and a nonzero displacement.
-/

namespace IsingModel
namespace Ambient

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

end Ambient
end IsingModel
