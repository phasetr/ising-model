import IsingModel.Peierls.PlusBoundary

/-!
# The `+`-expectation of the spin sign versus the down-spin probability (FV §3.7.2)

Since `σ_i = +1` for an up spin and `-1` for a down spin, pointwise `Spin.sign ℝ (σ i) =
1 - 2·[σ_i = -1]`. By linearity and normalization of the `+`-Gibbs expectation, the magnetization
`μ⁺(σ_i)` equals `1 - 2·μ⁺(σ_i = -1)`. This converts the Peierls down-spin bound into a lower bound
on the magnetization, the link to `m*(β) > 0`.

* `plusGibbsExpectation_one` — the `+`-expectation of the constant `1` is `1`.
* `plusGibbsExpectation_sign_eq` — `μ⁺(σ_i) = 1 - 2·μ⁺(σ_i = -1)`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedDecidableInType false in
/-- **The `+`-expectation of the constant `1` is `1`** (normalization). -/
theorem plusGibbsExpectation_one (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (p : IsingParams ℝ) (B : Finset ι) :
    plusGibbsExpectation G p B (fun _ => 1) = 1 := by
  rw [plusGibbsExpectation]
  simp only [one_mul]
  rw [← plusPartitionFunction]
  exact inv_mul_cancel₀ (plusPartitionFunction_pos' G p B).ne'

set_option linter.unusedDecidableInType false in
/-- **The magnetization equals `1 - 2·`(down-spin probability)**. -/
theorem plusGibbsExpectation_sign_eq (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (p : IsingParams ℝ) (B : Finset ι) (i : ι) :
    plusGibbsExpectation G p B (fun σ => Spin.sign ℝ (σ i))
      = 1 - 2 * plusGibbsExpectation G p B (fun σ => if σ i = Spin.down then 1 else 0) := by
  have hsign : ∀ s : Spin, Spin.sign ℝ s = 1 - 2 * (if s = Spin.down then (1 : ℝ) else 0) := by
    intro s
    cases s
    · simp only [Spin.sign, Spin.toSign, if_neg (by decide : Spin.up ≠ Spin.down)]
      norm_num
    · simp only [Spin.sign, Spin.toSign]
      norm_num
  rw [plusGibbsExpectation, plusGibbsExpectation]
  have hZne : plusPartitionFunction G p B ≠ 0 := (plusPartitionFunction_pos' G p B).ne'
  have hsum : ∑ σ ∈ plusConfigs B, Spin.sign ℝ (σ i) * boltzmannWeight G p σ
      = plusPartitionFunction G p B
        - 2 * ∑ σ ∈ plusConfigs B,
          (if σ i = Spin.down then (1 : ℝ) else 0) * boltzmannWeight G p σ := by
    rw [plusPartitionFunction, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun σ _ => by rw [hsign (σ i)]; ring)
  rw [hsum, mul_sub, inv_mul_cancel₀ hZne]
  ring

end IsingModel
