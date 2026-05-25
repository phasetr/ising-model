import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeProfileInputs
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderFiniteProfile

/-!
# GJ §17.5 Lemma 17.5.2 capstone — Dini-provider input

This module names the Dini-style derivative-profile input and packages it as a
`Lemma_17_5_2_DerivativeLimitProvider`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 Dini-order derivative-profile input**: on the
open high-temperature interval, each finite-volume beta-derivative profile
sequence is monotone or antitone in the exhaustion index. -/
def Lemma_17_5_2_DerivativeProfileDiniOrder
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) : Prop :=
  (∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
      Monotone
        (fun n =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)) ∨
    ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
      Antitone
        (fun n =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider from Dini-order
inputs**: finite derivative-profile continuity is discharged by
`lemma_17_5_2_finite_derivative_profile_continuous_beta`; the Dini-order,
limiting-derivative continuity, and pointwise convergence inputs then supply
the provider used by downstream capstone layers. -/
theorem lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (g' : ℝ → ℝ)
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint : Lemma_17_5_2_DerivativeProfilePointwiseLimit Λ J x z g') :
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z := by
  rcases horder with hmono | hanti
  · exact
      lemma_17_5_2_derivative_limit_provider_of_monotone_deriv_profiles_finite_continuous
        Λ J x z g' hmono hg_cont hpoint
  · exact
      lemma_17_5_2_derivative_limit_provider_of_antitone_deriv_profiles_finite_continuous
        Λ J x z g' hanti hg_cont hpoint

end Ambient
end IsingModel
