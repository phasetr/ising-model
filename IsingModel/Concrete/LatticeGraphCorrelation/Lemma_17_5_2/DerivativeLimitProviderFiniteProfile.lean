import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderCriteria

/-!
# GJ §17.5 Lemma 17.5.2 capstone — finite derivative-profile inputs

This module supplies the finite-volume continuity input needed by the
Dini-style derivative-limit provider criteria.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **GJ §17.5 Lemma 17.5.2 finite derivative-profile continuity**:
for each exhaustion stage, the beta-derivative profile of the finite-volume
two-point function is continuous in beta.  In the stage before `{x,z}` is
contained in the volume this is the derivative of the constant zero function;
afterward it is the explicit finite-volume beta-derivative formula, a finite
sum of continuous correlations. -/
theorem lemma_17_5_2_finite_derivative_profile_continuous_beta
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (n : ℕ) :
    Continuous
      (fun β =>
        deriv (fun β' =>
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β) := by
  by_cases hsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
  · let G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)
    let A : Finset (↑(Λ.volume n) : Type _) := liftFinset ({x, z} : Finset _) hsub
    let rhs : ℝ → ℝ := fun β =>
      J * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v =>
          IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ)
              (symmDiff A {u, v}) -
            IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A *
              IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {u, v},
          fun u v => by simp [Finset.pair_comm v u]⟩ e
    have hderiv_eq :
        ∀ β,
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β = rhs β := by
      intro β
      have hfun :
          (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) =
            fun β' => IsingModel.correlation G
              (⟨J, 0, β'⟩ : IsingParams ℝ) A := by
        funext β'
        rw [correlationAlongExhaustion_of_subset (IsingModel.latticeGraph d) Λ _ hsub,
          correlationΛ_apply]
      have hd := (IsingModel.hasDerivAt_correlation_beta G J β A).deriv
      rw [hfun]
      simpa [rhs, G, A] using hd
    have hrhs_cont : Continuous rhs := by
      dsimp [rhs]
      refine continuous_const.mul (continuous_finset_sum G.edgeFinset ?_)
      intro e he
      obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
      simp only [Sym2.lift_mk]
      exact (IsingModel.correlation_continuous_beta G J (symmDiff A {u, v})).sub
        ((IsingModel.correlation_continuous_beta G J A).mul
          (IsingModel.correlation_continuous_beta G J {u, v}))
    exact hrhs_cont.congr fun β => (hderiv_eq β).symm
  · have hderiv_eq :
        ∀ β,
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β = 0 := by
      intro β
      have hfun :
          (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) =
            fun _ => 0 := by
        funext β'
        exact correlationAlongExhaustion_of_not_subset
          (IsingModel.latticeGraph d) Λ _ hsub
      rw [hfun]
      simp
    exact continuous_const.congr fun β => (hderiv_eq β).symm

/-- Monotone Dini-provider criterion with the finite derivative-profile
continuity input discharged by
`lemma_17_5_2_finite_derivative_profile_continuous_beta`. -/
theorem
    lemma_17_5_2_derivative_limit_provider_of_monotone_deriv_profiles_finite_continuous
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (g' : ℝ → ℝ)
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
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
  lemma_17_5_2_derivative_limit_provider_of_monotone_deriv_profiles
    Λ J x z g'
    (fun n =>
      (lemma_17_5_2_finite_derivative_profile_continuous_beta Λ J x z n).continuousOn)
    hmono hg_cont hpoint

/-- Antitone Dini-provider criterion with the finite derivative-profile
continuity input discharged by
`lemma_17_5_2_finite_derivative_profile_continuous_beta`. -/
theorem
    lemma_17_5_2_derivative_limit_provider_of_antitone_deriv_profiles_finite_continuous
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (g' : ℝ → ℝ)
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
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
  lemma_17_5_2_derivative_limit_provider_of_antitone_deriv_profiles
    Λ J x z g'
    (fun n =>
      (lemma_17_5_2_finite_derivative_profile_continuous_beta Λ J x z n).continuousOn)
    hanti hg_cont hpoint

end Ambient
end IsingModel
