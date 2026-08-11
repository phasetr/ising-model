import IsingModel.AmbientLatticeSum.InfiniteHighTemp

/-!
# Divergence of the partition function along an exhaustion of an infinite type

`partitionFunctionAlongExhaustion G Λ p` reads at a stage `n` the partition function of the
subgraph of `G` induced by the stage volume `Λ.volume n`, for an arbitrary ambient graph
`G : SimpleGraph V` and an arbitrary exhaustion `Λ : Exhaustion V`.

Under `Ferromagnetic p` that sequence, and its logarithm, tend to `atTop`. Both statements
take `[Infinite V]`, the instance under which `Exhaustion.tendsto_card_atTop` sends the stage
cardinalities to `atTop`, together with `[DecidableEq V]` and the stagewise `Fintype`
instance on the edge set of the induced subgraph; those three are the only instance binders
here, and `Ferromagnetic p` is the only explicit hypothesis. Of those four binders,
`Ferromagnetic p` and `[Infinite V]` are the Prop-valued ones — `Infinite` is declared a
`Prop` class — while `[DecidableEq V]` and the `Fintype` instance carry data.
-/

namespace IsingModel

open Ambient

namespace Ambient

variable {V : Type*} [DecidableEq V]

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
