import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.ChebyshevRateBridge

/-!
# Hyperplane (ℓ∞) decay → `HasExponentialDecay` bridge (GJ §17.5)

Glimm–Jaffe §17.5 (p. 312) obtains, from the transfer matrix, exponential decay
of correlations `e^{-m·dist}` in the lattice hyperplane separation `dist`, which
on `ℤ^d` is the ℓ∞ (Chebyshev) distance `latticeDistanceInf`. Together with the
geometric bound `dist ≥ |x-y|/a₀` (`a₀ = d`), this yields decay at rate `m/d` in
the ℓ¹ distance `latticeDistance` used by the project's `HasExponentialDecay` /
`latticeMass` machinery.

This file records that bridge: a hyperplane-separation decay hypothesis on the
∞-volume truncated two-point function implies `HasExponentialDecay` at rate
`m/d` — so a future transfer-matrix decay estimate can be consumed as a
hypothesis, without constructing the transfer-matrix spectral operator.
-/

namespace IsingModel

namespace Ambient

/-- **Hyperplane (ℓ∞) decay implies ℓ¹ `HasExponentialDecay`** (GJ §17.5): if the
∞-volume truncated two-point function decays exponentially in the lattice
hyperplane separation (ℓ∞ distance) at rate `m`,
`|S^T_2(i,j)| ≤ A·e^{-m·|i-j|_∞}` for all `i ≠ j`, then it has the project's
ℓ¹ `HasExponentialDecay` at the reduced rate `m/d`. The reduction is the geometric
rate conversion `le_exp_neg_rate_latticeDistance_of_le_exp_neg_latticeDistanceInf`
(`|i-j|₁ ≤ d·|i-j|_∞`), lifted to the decay witness. This lets a transfer-matrix
hyperplane decay estimate feed directly into the `latticeMass` development without
the spectral operator. -/
theorem HasExponentialDecay_of_latticeDistanceInf_bound
    {d : ℕ} {Λ : Ambient.Exhaustion (Fin d → ℤ)} {p : IsingParams ℝ} {m A : ℝ}
    (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hbound : ∀ i j : Fin d → ℤ, i ≠ j →
      |truncated2Infinite (latticeGraph d) Λ p i j|
        ≤ A * Real.exp (-(m * (latticeDistanceInf d i j : ℝ)))) :
    HasExponentialDecay d Λ p (m / d) := by
  refine ⟨A, hA, fun i j hij => ?_⟩
  have h := le_exp_neg_rate_latticeDistance_of_le_exp_neg_latticeDistanceInf
    d i j hm hA (hbound i j hij)
  rwa [neg_mul]

end Ambient

end IsingModel
