import IsingModel.AmbientLatticeSum.InfiniteHighTemp

namespace IsingModel

open Ambient

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Moved: freeEnergyInfinite h-symmetry + monotonicity wrappers

The 6 freeEnergyInfinite h-symmetry + monotonicity wrappers now live in
`IsingModel.AmbientLatticeSumFInfHSymMono`.
The earlier import path is preserved by re-importing the new child.
-/

/-- **`log Z` tends to `∞` along any exhaustion of an infinite ambient
type**, under ferromagnetic parameters.

Direct application of the pointwise bound
`log_partitionFunctionAlongExhaustion_ge_card_mul_log_two_of_ferromagnetic`
(PR #165): `|Λ.volume n| · log 2 ≤ log Z_n` for every `n`. Combined
with `Exhaustion.tendsto_card_atTop` (|Λ.volume n| → ∞) and
`log 2 > 0`, the lower bound tends to `∞`; `Filter.tendsto_atTop_mono`
lifts this to `log Z_n → ∞`. -/
theorem log_partitionFunctionAlongExhaustion_tendsto_atTop
    [Infinite V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => Real.log (partitionFunctionAlongExhaustion G Λ p n))
      Filter.atTop Filter.atTop := by
  have hlog2_pos : (0 : ℝ) < Real.log 2 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h_card_tendsto :
      Filter.Tendsto (fun n => ((Λ.volume n).card : ℝ) * Real.log 2)
        Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop.comp Λ.tendsto_card_atTop).atTop_mul_const
      hlog2_pos
  exact Filter.tendsto_atTop_mono
    (fun n => log_partitionFunctionAlongExhaustion_ge_card_mul_log_two_of_ferromagnetic
      G Λ p hf n)
    h_card_tendsto

/-- **`Z` tends to `∞` along any exhaustion of an infinite ambient
type**, under ferromagnetic parameters. Follows from
`log_partitionFunctionAlongExhaustion_tendsto_atTop` via
`Real.tendsto_exp_atTop`. -/
theorem partitionFunctionAlongExhaustion_tendsto_atTop
    [Infinite V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto (partitionFunctionAlongExhaustion G Λ p)
      Filter.atTop Filter.atTop := by
  have h_log := log_partitionFunctionAlongExhaustion_tendsto_atTop G Λ p hf
  have h_comp := Real.tendsto_exp_atTop.comp h_log
  refine (Filter.tendsto_congr ?_).mp h_comp
  intro n
  exact Real.exp_log (IsingModel.partitionFunction_pos _ _)

end Ambient

end IsingModel
