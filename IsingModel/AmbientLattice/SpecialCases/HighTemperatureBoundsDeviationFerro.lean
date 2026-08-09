import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation

/-!
# The zero-field deviation bounds under `0 ≤ J` and `0 < β`

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume. All statements are at the parameter record `⟨J, 0, β⟩` and assume `0 ≤ J`
together with `0 < β`.

Under the additional hypothesis `0 < |Λ|`, the free energy exceeds `Real.log 2` by at most
`β * J * |E| / |Λ|`, and that excess is recorded again in the two-sided form
`0 ≤ f - Real.log 2 ≤ β * J * |E| / |Λ|`. Under `0 ≤ J` and `0 < β` alone, the logarithm of
the partition function satisfies `0 ≤ log Z - |Λ| * Real.log 2 ≤ β * J * |E|`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic f deviation bound at stage `n`**: under
`0 ≤ J, 0 < β`, `f_n - log 2 ≤ β·J·|E_n|/|Λ_n|`. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_deviation_bound_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_deviation_bound_exp
    G Λ J β (mul_nonneg hβ.le hJ) n hne

/-- **Along-ex ferromagnetic f deviation sandwich at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_deviation_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card) :
    0 ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
          (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_deviation_sandwich
    G Λ J β (mul_nonneg hβ.le hJ) n hne

/-- **Along-ex ferromagnetic log Z deviation sandwich at stage `n`**. -/
theorem
log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    0 ≤ Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - ((Λ.volume n).card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - ((Λ.volume n).card : ℝ) * Real.log 2
      ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_sandwich
    G Λ J β (mul_nonneg hβ.le hJ) n

end Ambient

end IsingModel
