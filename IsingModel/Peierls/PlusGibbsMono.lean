import IsingModel.Peierls.PlusGibbsSign

/-!
# Monotonicity of the `+`-Gibbs expectation (FV §3.7.2)

The `+`-Gibbs expectation `μ⁺(F) = (Z⁺)⁻¹ ∑ F·w` is monotone in the observable `F` (Boltzmann
weights are positive and the partition function is positive). In particular the magnetization
`μ⁺(σ_i)` is at most `1`, since `Spin.sign ℝ (σ i) ≤ 1` pointwise and `μ⁺(1) = 1`. This upper bound
supplies the coboundedness needed to push the per-stage Peierls bound to the infinite-volume
liminf.

* `plusGibbsExpectation_mono` — monotonicity of the expectation.
* `plusGibbsExpectation_sign_le_one` — `μ⁺(σ_i) ≤ 1`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedDecidableInType false in
/-- **Monotonicity of the `+`-expectation**: `F₁ ≤ F₂` pointwise implies `μ⁺(F₁) ≤ μ⁺(F₂)`. -/
theorem plusGibbsExpectation_mono (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (p : IsingParams ℝ) (B : Finset ι) (F₁ F₂ : Config ι → ℝ) (h : ∀ σ, F₁ σ ≤ F₂ σ) :
    plusGibbsExpectation G p B F₁ ≤ plusGibbsExpectation G p B F₂ := by
  rw [plusGibbsExpectation, plusGibbsExpectation]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (plusPartitionFunction_pos' G p B).le)
  exact Finset.sum_le_sum fun σ _ =>
    mul_le_mul_of_nonneg_right (h σ) (boltzmannWeight_pos G p σ).le

set_option linter.unusedDecidableInType false in
/-- **The magnetization is at most `1`**: `μ⁺(σ_i) ≤ 1`. -/
theorem plusGibbsExpectation_sign_le_one (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (p : IsingParams ℝ) (B : Finset ι) (i : ι) :
    plusGibbsExpectation G p B (fun σ => Spin.sign ℝ (σ i)) ≤ 1 := by
  rw [← plusGibbsExpectation_one G p B]
  refine plusGibbsExpectation_mono G p B _ _ (fun σ => ?_)
  cases h : σ i <;> simp [Spin.sign, Spin.toSign]

end IsingModel
