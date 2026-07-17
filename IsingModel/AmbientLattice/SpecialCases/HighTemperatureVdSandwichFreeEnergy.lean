import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaRegularity

/-!
# §18.5 strict `freeEnergyAlongExhaustion` cluster-expansion bounds

Narrow child module for the two §18.5 strict
`freeEnergyAlongExhaustion_lt_log_two_plus_high_temp_correction*`
along-exhaustion wrappers extracted from `HighTemperatureVdSandwichFE.lean`:

* `freeEnergyAlongExhaustion_lt_log_two_plus_high_temp_correction`
* `freeEnergyAlongExhaustion_lt_log_two_plus_high_temp_correction_ferromagnetic`

The general wrapper unfolds `freeEnergyAlongExhaustion` to the
ambient `freeEnergyΛ_lt_log_two_plus_high_temp_correction` lemma;
the ferromagnetic specialization derives `0 ≤ β * J` from `0 ≤ J`
and `0 < β` and reuses the general wrapper. Theorem names are
unchanged from the former `HighTemperatureVdSandwichFE` declarations.
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
