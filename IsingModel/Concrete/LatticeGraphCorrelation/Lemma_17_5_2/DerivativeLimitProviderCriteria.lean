import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProvider
import Mathlib.Topology.UniformSpace.Dini

/-!
# GJ §17.5 Lemma 17.5.2 capstone — derivative-limit provider criteria

This module records Dini-style sufficient criteria for the
`Lemma_17_5_2_DerivativeLimitProvider` input.  The criteria reduce the provider
proof to pointwise convergence of the finite-volume beta-derivative profiles
plus a monotonicity direction and continuity of the limiting derivative profile.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider criterion,
monotone form**: pointwise convergence of the finite-volume beta-derivative
profiles to a continuous limit upgrades to locally uniform convergence by
Dini's theorem when the profiles are stagewise monotone increasing on the
open high-temperature interval. -/
theorem lemma_17_5_2_derivative_limit_provider_of_monotone_deriv_profiles
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (g' : ℝ → ℝ)
    (hcont :
      ∀ n,
        ContinuousOn
          (fun β =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hmono :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Monotone
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β))
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β))) :
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z := by
  refine ⟨g', ?_⟩
  exact Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto
    hcont hmono hg_cont hpoint

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider criterion,
antitone form**: the decreasing-profile analogue of
`lemma_17_5_2_derivative_limit_provider_of_monotone_deriv_profiles`. -/
theorem lemma_17_5_2_derivative_limit_provider_of_antitone_deriv_profiles
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (g' : ℝ → ℝ)
    (hcont :
      ∀ n,
        ContinuousOn
          (fun β =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hanti :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Antitone
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β))
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β))) :
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z := by
  refine ⟨g', ?_⟩
  exact Antitone.tendstoLocallyUniformlyOn_of_forall_tendsto
    hcont hanti hg_cont hpoint

end Ambient
end IsingModel
