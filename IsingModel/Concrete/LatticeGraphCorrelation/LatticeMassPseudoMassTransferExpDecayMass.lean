import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferExpDecay

/-!
# ℤ^d high-temperature lower bound and positivity of the lattice mass (§17.5)

Instantiates at `IsingModel.latticeGraph d`, at zero external field and for an arbitrary
`Ambient.Exhaustion` of `Fin d → ℤ`, the high-temperature facts about the lattice mass. Its
value dominates `ENNReal.ofReal (-log (β * J * (2 * d)))` under `0 ≤ J`, `0 < β` and
`β * J * (2 * d)` below one. Strict positivity of the lattice mass needs more: besides the
same conditions it assumes `1 ≤ d` and `0 < β * J`, which is what makes the transferred rate
itself strictly positive.
-/

namespace IsingModel
namespace Ambient

/-- **Arbitrary-exhaustion high-temperature lattice-mass lower bound**:
for any exhaustion `Λ`, the Simon--Lieb high-temperature rate
`-log(βJ·2d)` belongs below `latticeMass d Λ ⟨J,0,β⟩`.

This is the exhaustion-uniform version of `latticeMass_ge_neg_log_of_high_temp`;
it combines `HasExponentialDecay_transfer_high_temp` with the `sSup` definition
of `latticeMass`.

References: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2, pp. 311--312. -/
theorem latticeMass_ge_neg_log_of_high_temp_exhaustion
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) :
    ENNReal.ofReal (-Real.log (β * J * ↑(2 * d))) ≤
    latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  have hβJD_nn : 0 ≤ β * J * ↑(2 * d) :=
    mul_nonneg (mul_nonneg hβ.le hJ) (Nat.cast_nonneg _)
  have hα_nn : 0 ≤ -Real.log (β * J * ↑(2 * d)) :=
    neg_nonneg.mpr (Real.log_nonpos hβJD_nn hlt.le)
  exact latticeMass_ge_of_HasExponentialDecay hα_nn
    (HasExponentialDecay_transfer_high_temp Λ hJ hβ hlt)

/-- **Arbitrary-exhaustion positive lattice mass in the high-temperature regime**:
if `0 < βJ` and `βJ·2d < 1` with `d ≥ 1`, then every exhaustion has positive
`latticeMass`.

The proof uses the transferred high-temperature decay rate
`-log(βJ·2d)`, which is strictly positive when `0 < βJ·2d < 1`.

Reference: Glimm--Jaffe §17.5 pp. 304--306. -/
theorem latticeMass_pos_of_high_temp_exhaustion
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ : 0 < β * J)
    (hlt : β * J * ↑(2 * d) < 1) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  have hβJD_pos : 0 < β * J * ↑(2 * d) :=
    mul_pos hβJ (Nat.cast_pos.mpr (by omega))
  have hα_pos : 0 < -Real.log (β * J * ↑(2 * d)) :=
    neg_pos.mpr (Real.log_neg hβJD_pos hlt)
  exact latticeMass_pos_of_HasExponentialDecay hα_pos
    (HasExponentialDecay_transfer_high_temp Λ hJ hβ hlt)

end Ambient
end IsingModel
