import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaRegularity

/-!
# A strict zero-field free-energy bound in the cluster-expansion convergence regime

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume.

Under `0 ≤ β * J`, `0 < |Λ|` and the convergence condition
`(1 + Real.tanh (β * J)) ^ |E| < 2`, the free energy at the parameter record `⟨J, 0, β⟩` is
strictly below `Real.log 2 + (|E| / |Λ|) * Real.log (Real.cosh (β * J)) + Real.log 2 / |Λ|`.
The same bound is stated under `0 ≤ J` together with `0 < β` in place of `0 ≤ β * J`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion: strict `freeEnergyAlongExhaustion` upper
bound in cluster-expansion convergence regime** (§18.5 along-ex
wrap of #1527). -/
theorem
freeEnergyAlongExhaustion_lt_log_two_plus_high_temp_correction
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card < 2) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n <
      Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card *
          Real.log (Real.cosh (β * J)) +
        Real.log 2 / (Λ.volume n).card := by
  unfold freeEnergyAlongExhaustion
  exact freeEnergyΛ_lt_log_two_plus_high_temp_correction
    G (Λ.volume n) J β hβJ hne h_pow

/-- **Along-exhaustion: strict `freeEnergyAlongExhaustion` upper
bound in cluster-expansion convergence regime (ferromagnetic)**
(§18.5 along-ex wrap, ferro). -/
theorem
freeEnergyAlongExhaustion_lt_log_two_plus_high_temp_correction_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card < 2) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n <
      Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card *
          Real.log (Real.cosh (β * J)) +
        Real.log 2 / (Λ.volume n).card :=
  freeEnergyAlongExhaustion_lt_log_two_plus_high_temp_correction
    G Λ J β (mul_nonneg hβ.le hJ) n hne h_pow

end Ambient
end IsingModel
