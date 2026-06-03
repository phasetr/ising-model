import IsingModel.TransferMatrix.GibbsTwoPoint
import IsingModel.TransferMatrix.OneDimCorrelationLength

/-!
# Gibbs-form exponential decay of the 1D Ising two-point function (GJ §17.1)

The transfer-matrix two-point analysis is stated about the abstract ratio
`twoPointCorrelation` (`OneDimTwoPoint.lean`, `OneDimCorrelationLength.lean`).
Composing it with the Gibbs/transfer-matrix bridge
`correlation_cycleGraph_eq_twoPointCorrelation` (#3530) restates the exact
exponential decay of the 1D Ising correlation directly for the project's **Gibbs**
`correlation` on the cyclic chain:

* closed eigenvalue form and `tanh` ratio form of
  `correlation (cycleGraph N) ⟨J,0,β⟩ {0,n}`;
* `correlation (cycleGraph (n+k+3)) ⟨J,0,β⟩ {0,n} → (tanh βJ)ⁿ` as `k → ∞`;
* the same limit as the pure exponential `exp(-m·n)` at the inverse correlation
  length `m = -log tanh βJ`.

Throughout we parametrise the chain length as `N = n + k + 3` so that the two
insertion sites `0` and `n` are always valid (`n < N`) for every `k`, letting the
endpoint distance `n` stay fixed while the volume `N → ∞`.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1.
-/

namespace IsingModel

namespace TransferMatrix

open Filter Topology SimpleGraph

/-- **Gibbs two-point correlation in closed eigenvalue form** (Glimm–Jaffe §17.1):
for `0 < n < N` (`N = k+3`),
`correlation (cycleGraph N) ⟨J,0,β⟩ {0,n}
  = (λ₋ⁿ·λ₊^{N-n} + λ₊ⁿ·λ₋^{N-n}) / (λ₊ᴺ + λ₋ᴺ)`.
Direct from the Gibbs/transfer-matrix bridge `correlation_cycleGraph_eq_twoPointCorrelation`
and `twoPointCorrelation_eq`. -/
theorem correlation_cycleGraph_eq_eigenvaluePow (k n : ℕ) (hn : n < k + 3)
    (hn0 : 0 < n) {J β : ℝ} :
    correlation (cycleGraph (k + 3)) (⟨J, 0, β⟩ : IsingParams ℝ) {0, ⟨n, hn⟩}
      = (transferEigenvalueBot (β * J) ^ n
            * transferEigenvalueTop (β * J) ^ (k + 3 - n)
          + transferEigenvalueTop (β * J) ^ n
            * transferEigenvalueBot (β * J) ^ (k + 3 - n))
        / (transferEigenvalueTop (β * J) ^ (k + 3)
            + transferEigenvalueBot (β * J) ^ (k + 3)) := by
  rw [correlation_cycleGraph_eq_twoPointCorrelation k n hn hn0, twoPointCorrelation_eq]

/-- **Gibbs two-point correlation in `tanh` ratio form** (Glimm–Jaffe §17.1): for
`0 < n < N` (`N = k+3`), with `r = λ₋/λ₊ = tanh βJ`,
`correlation (cycleGraph N) ⟨J,0,β⟩ {0,n} = (rⁿ + r^{N-n}) / (1 + rᴺ)`.
The dominant eigenvalue `λ₊ᴺ` cancels between numerator and denominator. -/
theorem correlation_cycleGraph_eq_ratio (k n : ℕ) (hn : n < k + 3) (hn0 : 0 < n)
    {J β : ℝ} :
    correlation (cycleGraph (k + 3)) (⟨J, 0, β⟩ : IsingParams ℝ) {0, ⟨n, hn⟩}
      = ((transferEigenvalueBot (β * J) / transferEigenvalueTop (β * J)) ^ n
          + (transferEigenvalueBot (β * J) / transferEigenvalueTop (β * J))
              ^ (k + 3 - n))
        / (1 + (transferEigenvalueBot (β * J) / transferEigenvalueTop (β * J))
            ^ (k + 3)) := by
  rw [correlation_cycleGraph_eq_twoPointCorrelation k n hn hn0,
    twoPointCorrelation_eq_ratio (β * J) n (k + 3) hn.le]

/-- The chain length `N = n + k + 3` tends to infinity as `k → ∞`. -/
theorem tendsto_nat_add_offset_atTop (n : ℕ) :
    Tendsto (fun k : ℕ => n + k + 3) atTop atTop := by
  refine tendsto_atTop_mono ?_ tendsto_id
  intro k
  simp only [id_eq]
  omega

/-- **Exponential decay of the Gibbs 1D Ising two-point function** (Glimm–Jaffe §17.1):
for `a = β J > 0` and a fixed endpoint distance `0 < n`, the Gibbs correlation of the
two endpoint spins on the cyclic chain converges to the geometric decay
`⟨σ₀σₙ⟩ → (tanh βJ)ⁿ` as the volume `N = n+k+3 → ∞`.  This is the exact 1D Ising
correlation decay with rate `−log tanh βJ`, stated for the project's Gibbs
`correlation` (parametrising `N = n+k+3` keeps the sites `0`, `n` valid for all `k`). -/
theorem tendsto_correlation_cycleGraph {J β : ℝ} (hβJ : 0 < β * J) {n : ℕ}
    (hn0 : 0 < n) :
    Tendsto (fun k : ℕ =>
        correlation (cycleGraph (n + k + 3)) (⟨J, 0, β⟩ : IsingParams ℝ)
          {0, ⟨n, by omega⟩})
      atTop (𝓝 (Real.tanh (β * J) ^ n)) := by
  refine (tendsto_twoPointCorrelation (β * J) hβJ n).comp
    (tendsto_nat_add_offset_atTop n) |>.congr (fun k => ?_)
  rw [Function.comp_apply,
    correlation_cycleGraph_eq_twoPointCorrelation (n + k) n (by omega) hn0]

/-- **Gibbs 1D Ising two-point decay at the correlation length** (Glimm–Jaffe §17.1,
§17.5): for `a = β J > 0` and fixed `0 < n`, the Gibbs correlation converges to the
pure exponential `exp(-m·n)` with mass `m = correlationMass (βJ) = -log tanh βJ`
(the inverse correlation length), `⟨σ₀σₙ⟩ → exp(-m·n)` as `N = n+k+3 → ∞`. -/
theorem tendsto_correlation_cycleGraph_exp_neg_mass {J β : ℝ} (hβJ : 0 < β * J)
    {n : ℕ} (hn0 : 0 < n) :
    Tendsto (fun k : ℕ =>
        correlation (cycleGraph (n + k + 3)) (⟨J, 0, β⟩ : IsingParams ℝ)
          {0, ⟨n, by omega⟩})
      atTop (𝓝 (Real.exp (-(correlationMass (β * J)) * n))) := by
  rw [← tanh_pow_eq_exp_neg_mass hβJ n]
  exact tendsto_correlation_cycleGraph hβJ hn0

end TransferMatrix

end IsingModel
