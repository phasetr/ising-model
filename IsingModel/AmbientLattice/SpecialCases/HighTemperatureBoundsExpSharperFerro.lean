import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper

/-!
# Exponential upper bounds at zero field under `0 ≤ J` and `0 < β`

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume. All statements assume `0 ≤ J` together with `0 < β`.

At the parameter record `⟨J, 0, β⟩` the partition function is at most
`2 ^ |Λ| * Real.exp (β * J * |E|)` and its logarithm is at most
`|Λ| * Real.log 2 + β * J * |E|`; under the additional hypothesis `0 < |Λ|` the free energy
is at most `Real.log 2 + β * J * |E| / |Λ|`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic Z sharper upper bound at stage `n`**:
under `0 ≤ J, 0 < β`,
`Z_n ≤ 2^|Λ_n| · exp(β·J·|E_n|)`. Stage-`n` Λ-level ferromagnetic
specialization. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ (Λ.volume n).card *
          Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp
    G Λ J β (mul_nonneg hβ.le hJ) n

/-- **Along-ex ferromagnetic log Z sharper upper bound at stage `n`**:
under `0 ≤ J, 0 < β`,
`log Z_n ≤ |Λ_n|·log 2 + β·J·|E_n|`. -/
theorem
log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      ≤ ((Λ.volume n).card : ℝ) * Real.log 2
        + β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp
    G Λ J β (mul_nonneg hβ.le hJ) n

/-- **Along-ex ferromagnetic f sharper upper bound at stage `n`**:
under `0 ≤ J, 0 < β` and `0 < |Λ_n|`,
`f_n ≤ log 2 + β·J·|E_n|/|Λ_n|`. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2 +
          β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp
    G Λ J β (mul_nonneg hβ.le hJ) n hne

end Ambient

end IsingModel
