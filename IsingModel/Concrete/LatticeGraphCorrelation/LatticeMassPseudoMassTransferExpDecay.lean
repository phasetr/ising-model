import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeCorrelationInequalities
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationSymmetry
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Inequalities.HighTemp
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature.ExpDecay

/-!
# ℤ^d extraction and transfer of exponential-decay rates

Instantiates at `IsingModel.latticeGraph d` the moves on the exponential-decay predicate that
the pseudo-mass bridge needs. From strict positivity of the lattice mass of one
`Ambient.Exhaustion` a strictly positive validating rate is extracted, with no further
hypothesis. Between two exhaustions a validating rate transfers whenever the parameter record
is ferromagnetic, the rate and the witnessing constant carrying over unchanged. Finally, at
zero external field, the transferred Simon-Lieb high-temperature rate
`-log (β * J * (2 * d))` validates the predicate for an arbitrary exhaustion, under `0 ≤ J`,
`0 < β` and `β * J * (2 * d)` below one.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Extract positive decay rate from positive lattice mass** (GJ §17.1):
if `latticeMass d Λ p > 0`, there exists `α : NNReal` with `0 < (α : ℝ)` and
`HasExponentialDecay d Λ p (α : ℝ)`.

Proof: by `lt_sSup_iff`, a positive supremum of the image set contains some
element `(α : ENNReal) > 0`; coercing via `ENNReal.coe_pos` and
`NNReal.coe_pos` yields a positive real decay rate.

**GJ §17.1 context**: the positivity of the lattice mass (= inverse correlation
length) directly produces an exponential decay witness, connecting the abstract
`latticeMass` definition to the `HasExponentialDecay` predicate. -/
theorem HasExponentialDecay_of_latticeMass_pos
    {d : ℕ} {Λ : Ambient.Exhaustion (Fin d → ℤ)} {p : IsingParams ℝ}
    (h : 0 < latticeMass d Λ p) :
    ∃ α : NNReal, 0 < (α : ℝ) ∧ HasExponentialDecay d Λ p (α : ℝ) := by
  unfold latticeMass at h
  rw [lt_sSup_iff] at h
  obtain ⟨y, hy_mem, hy_pos⟩ := h
  rw [Set.mem_image] at hy_mem
  obtain ⟨α, hα_decay, hα_eq⟩ := hy_mem
  rw [← hα_eq] at hy_pos
  exact ⟨α, NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hy_pos), hα_decay⟩

/-- **Transfer `HasExponentialDecay` across exhaustions**:
for ferromagnetic `p`, if `HasExponentialDecay d Λ p α` holds for some
exhaustion `Λ`, then it holds for any other exhaustion `Λ'`.

Proof: the truncated 2-point function is exhaustion-independent for ferromagnetic
parameters (`truncated2Infinite_indep_exhaustion`), so the bound transfers directly
from `Λ` to `Λ'` with the same constant `C` and rate `α`. -/
theorem HasExponentialDecay_transfer_exhaustion
    {d : ℕ} (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    {p : IsingParams ℝ} {α : ℝ}
    (hf : Ferromagnetic p)
    (h : HasExponentialDecay d Λ p α) :
    HasExponentialDecay d Λ' p α := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun i j hij => ?_⟩
  rw [truncated2Infinite_indep_exhaustion (IsingModel.latticeGraph d) Λ' Λ p hf i j]
  exact hbound i j hij

/-- **Uniform high-temperature exponential decay across exhaustions**:
the Simon--Lieb high-temperature decay rate from `cubicExhaustion` transfers to any
exhaustion `Λ` under ferromagnetic `h = 0` parameters.

This is the reusable uniform-in-exhaustion form needed by the Step 117l
pseudo-mass/lattice-mass bridge: the witness constant and rate are independent of
the target exhaustion because `truncated2Infinite` is exhaustion-independent under
ferromagnetic parameters.

References: Glimm--Jaffe §17.5 Lemma 17.5.2, pp. 311--312; Simon 1980,
Comm. Math. Phys. 77, 111--126; Lieb 1980, Comm. Math. Phys. 77, 127--135. -/
theorem HasExponentialDecay_transfer_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        (-Real.log (β * J * ↑(2 * d))) :=
  HasExponentialDecay_transfer_exhaustion (cubicExhaustion d) Λ
    (p := (⟨J, 0, β⟩ : IsingParams ℝ))
    ⟨hJ, le_refl 0, hβ⟩
    (hasExponentialDecay_of_high_temp (mul_nonneg hβ.le hJ) hlt)

end Ambient

end IsingModel
