import IsingModel.AmbientFKG
import IsingModel.Conditioning.CorrelationClosed.GeneralField

/-!
# Along-exhaustion general external-field high-temperature Gibbs-expectation expansion

Along-exhaustion lift of
`gibbsExpectation_high_temp_expansion_general_h_subset_form` (GJ §18.3/§18.5):
the per-stage Gibbs expectation of an arbitrary observable family admits the
general-`h` subset ratio form whose inner σ-sums carry the external-field
weight `exp(β h ∑_i σ_i)`. Relevant to the infinite-volume limit, where
thermal averages are studied along an exhaustion `Λ ↑ V`.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion general-`h` Gibbs-expectation subset expansion
(GJ §18.3/§18.5)**: for an observable family
`F : (n : ℕ) → Config (↑(Λ.volume n)) → ℝ` and Ising parameter
`p = (J, h, β)`, at every stage `n`,
\[
\langle F_n \rangle^{\Lambda_n}_p =
  \frac{\sum_{X \subseteq E_n} (\tanh\beta J)^{|X|}
      \sum_\sigma F_n(\sigma) (\prod_{e \in X} \sigma_e) e^{\beta h \sum_i \sigma_i}}
       {\sum_{X \subseteq E_n} (\tanh\beta J)^{|X|}
      \sum_\sigma (\prod_{e \in X} \sigma_e) e^{\beta h \sum_i \sigma_i}}.
\]
Direct lift of
`IsingModel.gibbsExpectation_high_temp_expansion_general_h_subset_form`
through `gibbsExpectationAlongExhaustion G Λ p F n
= gibbsExpectation (inducedGraph G (Λ.volume n)) p (F n)`.

References: GJ §18.3, pp. 378–386; FV §3.7.3, eqs. (3.41)–(3.46), pp. 116–117. -/
theorem gibbsExpectationAlongExhaustion_high_temp_expansion_general_h_subset_form
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (F : (n : ℕ) → Config (↑(Λ.volume n) : Type _) → ℝ) (n : ℕ) :
    gibbsExpectationAlongExhaustion G Λ p F n =
      (∑ X ∈ (inducedGraph G (Λ.volume n)).edgeFinset.powerset,
        Real.tanh (p.β * p.J) ^ X.card *
          ∑ σ : Config ↑(Λ.volume n),
            F n σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
            Real.exp (p.β * p.h * ∑ i : ↑(Λ.volume n), Spin.sign ℝ (σ i))) /
      (∑ X ∈ (inducedGraph G (Λ.volume n)).edgeFinset.powerset,
        Real.tanh (p.β * p.J) ^ X.card *
          ∑ σ : Config ↑(Λ.volume n),
            (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
            Real.exp (p.β * p.h * ∑ i : ↑(Λ.volume n), Spin.sign ℝ (σ i))) := by
  rw [gibbsExpectationAlongExhaustion_apply]
  exact IsingModel.gibbsExpectation_high_temp_expansion_general_h_subset_form
    (inducedGraph G (Λ.volume n)) p (F n)

end Ambient

end IsingModel
