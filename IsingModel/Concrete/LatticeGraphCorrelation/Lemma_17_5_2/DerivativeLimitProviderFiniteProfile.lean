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

/-- **GJ §17.5 Lemma 17.5.2 finite derivative-profile formula**: once the
exhaustion stage contains the target pair `{x,z}`, the beta derivative of the
finite-exhaustion two-point function is the explicit finite Lebowitz edge sum.

This is the concrete finite-volume derivative calculation used before the
derivative-limit provider and HLS denominator comparison are applied. -/
theorem lemma_17_5_2_finite_derivative_profile_eq_beta_edge_sum
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) {n : ℕ}
    (hsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume n) :
    ∀ β : ℝ,
      let G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)
      let A : Finset (↑(Λ.volume n) : Type _) :=
        liftFinset ({x, z} : Finset _) hsub
      deriv (fun β' =>
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β =
        J * ∑ e ∈ G.edgeFinset,
          Sym2.lift ⟨fun u v =>
            IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ)
                (symmDiff A {u, v}) -
              IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A *
                IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {u, v},
            fun u v => by simp [Finset.pair_comm v u]⟩ e := by
  intro β
  let G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)
  let A : Finset (↑(Λ.volume n) : Type _) := liftFinset ({x, z} : Finset _) hsub
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
  simpa [G, A]
    using hd

/-- **GJ §17.5 Lemma 17.5.2 finite derivative-profile zero formula**: before
the exhaustion stage contains the target pair `{x,z}`, the finite-exhaustion
two-point function is identically zero, hence its beta derivative is zero. -/
theorem lemma_17_5_2_finite_derivative_profile_eq_zero_of_not_subset
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) {n : ℕ}
    (hsub : ¬ ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume n) :
    ∀ β : ℝ,
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

/-- **GJ §17.5 Lemma 17.5.2 all-stage finite derivative-profile bound**:
on a closed high-temperature beta interval, the finite beta-derivative profile
is bounded by the Lebowitz/susceptibility constant at every exhaustion stage.

The covered-stage branch uses the finite-volume high-temperature derivative
estimate.  The uncovered-stage branch is new here: the zero formula
`lemma_17_5_2_finite_derivative_profile_eq_zero_of_not_subset` makes the bound
immediate, so no eventual containment restriction is needed for this finite
profile estimate. -/
theorem lemma_17_5_2_finite_deriv_abs_le_high_temp_on_Icc_all_stages
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J)
    {a b β₁ β₂ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ∀ n, ∀ β ∈ Set.Icc β₁ β₂,
      |deriv (fun β' =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
        J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 +
          J * (4 * ↑d) := by
  intro n β hβ
  by_cases hsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
  · have hx_mem : x ∈ Λ.volume n := hsub (by simp)
    have hz_mem : z ∈ Λ.volume n := hsub (by simp)
    let rx : ↑(Λ.volume n) := ⟨x, hx_mem⟩
    let rz : ↑(Λ.volume n) := ⟨z, hz_mem⟩
    have hrxz : rx ≠ rz := by
      intro heq
      exact hxz (congrArg Subtype.val heq)
    have hlift :
        Ambient.liftFinset ({x, z} : Finset (Fin d → ℤ)) hsub =
          ({rx, rz} : Finset (↑(Λ.volume n))) := by
      ext u
      simp [Ambient.mem_liftFinset, rx, rz, Subtype.ext_iff]
    obtain ⟨dval, hdval, habs⟩ :=
      lemma_17_5_2_beta_deriv_abs_le_high_temp
        Λ J hJ a b ha hab hlt n rx rz hrxz β (hβ_mem β hβ)
    let fAlong : ℝ → ℝ := fun β' =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n
    let fFinite : ℝ → ℝ := fun β' =>
      IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (⟨J, 0, β'⟩ : IsingParams ℝ) {rx, rz}
    have hf_eq : fAlong = fFinite := by
      funext β'
      simp only [fAlong, fFinite]
      rw [Ambient.correlationAlongExhaustion_of_subset
        (G := IsingModel.latticeGraph d) (Λ := Λ)
        (p := (⟨J, 0, β'⟩ : IsingParams ℝ)) hsub, Ambient.correlationΛ_apply,
        hlift]
    have hderiv_along : HasDerivAt fAlong dval β := by
      simpa [fAlong, fFinite, hf_eq] using hdval
    have hderiv_eq :
        deriv (fun β' =>
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β = dval := by
      simpa [fAlong] using hderiv_along.deriv
    simpa [hderiv_eq] using habs
  · have hzero :=
      lemma_17_5_2_finite_derivative_profile_eq_zero_of_not_subset
        Λ J x z hsub β
    have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by
      linarith
    have hb_pos : 0 < b := ha.trans_le hab
    have hM_nn :
        0 ≤ b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) :=
      div_nonneg
        (mul_nonneg (mul_nonneg hb_pos.le hJ) (Nat.cast_nonneg _))
        hdenom_b.le
    have hC_nn :
        0 ≤ J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 +
            J * (4 * ↑d) :=
      add_nonneg
        (mul_nonneg hJ (pow_nonneg hM_nn 2))
        (mul_nonneg hJ (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
    simpa [hzero] using hC_nn

/-- **GJ §17.5 Lemma 17.5.2 limiting derivative-profile bound**:
if the finite derivative profiles have a derivative-limit provider, then the
all-stage finite high-temperature derivative estimate passes to the limiting
derivative profile on the same closed beta interval. -/
theorem lemma_17_5_2_derivative_limit_profile_abs_le_high_temp_on_Icc
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J)
    {a b β₁ β₂ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlt : b * J * ↑(2 * d) < 1)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hprovider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z) :
    ∃ g' : ℝ → ℝ,
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) ∧
      ∀ β ∈ Set.Icc β₁ β₂,
        |g' β| ≤
          J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 +
            J * (4 * ↑d) := by
  obtain ⟨g', hderiv_lim⟩ := hprovider
  refine ⟨g', hderiv_lim, ?_⟩
  intro β hβ
  have hpoint :
      Filter.Tendsto
        (fun n =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        Filter.atTop (nhds (g' β)) :=
    hderiv_lim.tendsto_at (hIcc hβ)
  refine le_of_tendsto ((continuous_abs.tendsto (g' β)).comp hpoint) ?_
  exact Filter.Eventually.of_forall fun n =>
    lemma_17_5_2_finite_deriv_abs_le_high_temp_on_Icc_all_stages
      Λ J hJ ha hab hlt hβ_mem hxz n β hβ

/-- **GJ §17.5 Lemma 17.5.2 infinite beta-derivative bound**:
under a derivative-limit provider, the finite all-stage high-temperature
derivative estimate gives the same absolute bound for the beta derivative of
the infinite-volume two-point function on the closed interval. -/
theorem lemma_17_5_2_correlationInfinite_deriv_abs_le_high_temp_on_Icc
    {d : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    {a b β₁ β₂ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlt : b * J * ↑(2 * d) < 1)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hprovider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z) :
    ∀ β ∈ Set.Icc β₁ β₂,
      |deriv (fun β' =>
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}) β| ≤
        J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 +
          J * (4 * ↑d) := by
  obtain ⟨g', hderiv_lim, hbound⟩ :=
    lemma_17_5_2_derivative_limit_profile_abs_le_high_temp_on_Icc
      Λ J hJ_pos.le ha hab hlt hIcc hβ_mem hxz hprovider
  intro β hβ
  have hdiff :=
    correlationInfinite_hasDerivAt_beta_of_tendstoLocallyUniformlyOn_deriv
      hd Λ x z hxz J hJ_pos g' isOpen_Ioo (subset_refl _) hderiv_lim β (hIcc hβ)
  have hderiv :
      deriv (fun β' =>
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}) β = g' β :=
    hdiff.deriv
  simpa [hderiv] using hbound β hβ

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
    have hderiv_eq : ∀ β,
        deriv (fun β' =>
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β = rhs β := by
      intro β
      simpa [rhs, G, A] using
        lemma_17_5_2_finite_derivative_profile_eq_beta_edge_sum
          Λ J x z hsub β
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
      exact lemma_17_5_2_finite_derivative_profile_eq_zero_of_not_subset
        (Λ := Λ) (J := J) (x := x) (z := z) (n := n) hsub
    exact continuous_const.congr fun β => (hderiv_eq β).symm

/-- **GJ §17.5 Lemma 17.5.2 limiting derivative-profile continuity**:
under a derivative-limit provider, the locally uniform limit of the finite
beta-derivative profiles is continuous on the open high-temperature region.

The finite-profile continuity input is the concrete theorem
`lemma_17_5_2_finite_derivative_profile_continuous_beta`; the passage to the
limit uses the standard locally-uniform-limit continuity theorem. -/
theorem lemma_17_5_2_derivative_limit_profile_continuousOn_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ)
    (hprovider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z) :
    ∃ g' : ℝ → ℝ,
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) ∧
      ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  obtain ⟨g', hderiv_lim⟩ := hprovider
  refine ⟨g', hderiv_lim, hderiv_lim.continuousOn ?_⟩
  exact Filter.Frequently.of_forall fun n =>
    (lemma_17_5_2_finite_derivative_profile_continuous_beta Λ J x z n).continuousOn

/-- **GJ §17.5 Lemma 17.5.2 limiting derivative-profile continuity,
closed-interval form**: on each closed beta interval inside the
high-temperature region, the derivative-limit provider gives a uniformly
convergent finite derivative-profile sequence whose limit is continuous on that
closed interval. -/
theorem lemma_17_5_2_derivative_limit_profile_continuousOn_Icc
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ)
    {β₁ β₂ : ℝ}
    (hprovider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) :
    ∃ g' : ℝ → ℝ,
      TendstoUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Icc β₁ β₂) ∧
      ContinuousOn g' (Set.Icc β₁ β₂) := by
  obtain ⟨g', htend⟩ :=
    lemma_17_5_2_derivative_limit_provider_tendstoUniformlyOn_Icc
      (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) hprovider hIcc
  refine ⟨g', htend, htend.continuousOn ?_⟩
  exact Filter.Frequently.of_forall fun n =>
    (lemma_17_5_2_finite_derivative_profile_continuous_beta Λ J x z n).continuousOn

/-- **GJ §17.5 Lemma 17.5.2 infinite beta-derivative continuity**:
under a derivative-limit provider, the beta derivative of the infinite-volume
two-point function is continuous throughout the open high-temperature region.

The proof first passes finite derivative-profile continuity to the provider
witness, then identifies that witness pointwise with the infinite-volume beta
derivative. -/
theorem lemma_17_5_2_correlationInfinite_deriv_continuousOn_high_temp
    {d : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hprovider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z) :
    ContinuousOn
      (fun β =>
        deriv (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}) β)
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  obtain ⟨g', hderiv_lim, hg_cont⟩ :=
    lemma_17_5_2_derivative_limit_profile_continuousOn_high_temp
      Λ J x z hprovider
  refine hg_cont.congr ?_
  intro β hβ
  exact
    (correlationInfinite_hasDerivAt_beta_of_tendstoLocallyUniformlyOn_deriv
      hd Λ x z hxz J hJ_pos g' isOpen_Ioo (subset_refl _) hderiv_lim β hβ).deriv

/-- **GJ §17.5 Lemma 17.5.2 infinite beta differentiability**: under a
derivative-limit provider, the infinite-volume two-point function is
differentiable throughout the open high-temperature region. -/
theorem lemma_17_5_2_correlationInfinite_differentiableOn_high_temp
    {d : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hprovider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z) :
    DifferentiableOn ℝ
      (fun β =>
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  obtain ⟨g', hderiv_lim⟩ := hprovider
  intro β hβ
  exact
    (correlationInfinite_hasDerivAt_beta_of_tendstoLocallyUniformlyOn_deriv
      hd Λ x z hxz J hJ_pos g' isOpen_Ioo (subset_refl _) hderiv_lim β hβ).differentiableAt
      |>.differentiableWithinAt

/-- **GJ §17.5 Lemma 17.5.2 infinite `C^1` beta regularity**: under a
derivative-limit provider, the infinite-volume two-point function is `C^1` on
the open high-temperature region. -/
theorem lemma_17_5_2_correlationInfinite_contDiffOn_one_high_temp
    {d : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hprovider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z) :
    ContDiffOn ℝ 1
      (fun β =>
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  let s : Set ℝ := Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))
  let f : ℝ → ℝ := fun β =>
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
  have hs : IsOpen s := isOpen_Ioo
  change ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1) f s
  rw [contDiffOn_succ_iff_deriv_of_isOpen hs]
  refine ⟨?_, ?_, ?_⟩
  · exact
      lemma_17_5_2_correlationInfinite_differentiableOn_high_temp
        hd Λ J hJ_pos hxz hprovider
  · intro hzero
    cases hzero
  · rw [contDiffOn_zero]
    exact
      lemma_17_5_2_correlationInfinite_deriv_continuousOn_high_temp
        hd Λ J hJ_pos hxz hprovider

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

/-- **GJ §17.5 Lemma 17.5.2 finite β-derivative increment vanishes before
coverage**: if the exhaustion stage `k + 1` does not yet contain the pair
`{x,z}`, then neither does stage `k` (by monotonicity of the exhaustion), so
both finite β-derivative profiles vanish identically and their consecutive-stage
increment is zero.

This pins down the support of the derivative increments: any concrete
convergence-rate control of `|F_{k+1} - F_k|` only needs to address the stages
that already contain the pair.  Part of Issue #2931. -/
theorem lemma_17_5_2_finite_derivative_increment_eq_zero_of_not_subset
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) {k : ℕ}
    (hsub : ¬ ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume (k + 1)) (β : ℝ) :
    deriv (fun β' =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β = 0 ∧
    deriv (fun β' =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β = 0 := by
  have hk : ¬ ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k :=
    fun h => hsub (h.trans (Λ.mono (Nat.le_succ k)))
  exact
    ⟨lemma_17_5_2_finite_derivative_profile_eq_zero_of_not_subset Λ J x z hk β,
      lemma_17_5_2_finite_derivative_profile_eq_zero_of_not_subset Λ J x z hsub β⟩

/-- **GJ §17.5 Lemma 17.5.2 uniform increment bound for the finite
β-derivative profiles**: on a closed high-temperature interval the
consecutive-stage increment `F_{k+1} - F_k` is bounded in absolute value by
twice the all-stage finite high-temperature derivative bound, uniformly in the
stage `k` and the point `β`.

This is the explicit (stage-uniform) magnitude control of the derivative
increments: it follows from the all-stage finite high-temperature derivative
bound `lemma_17_5_2_finite_deriv_abs_le_high_temp_on_Icc_all_stages` at stages
`k` and `k + 1` and the triangle inequality.  The bound is uniform but not yet
summable; sharpening it to a summable (geometric) bound via the finite-volume
convergence rate is the substantive remaining input tracked by Issue #2931. -/
theorem lemma_17_5_2_finite_derivative_increment_abs_le_high_temp_on_Icc_all_stages
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J)
    {a b β₁ β₂ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ∀ k, ∀ β ∈ Set.Icc β₁ β₂,
      |deriv (fun β' =>
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β -
        deriv (fun β' =>
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β| ≤
        2 * (J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 +
          J * (4 * ↑d)) := by
  intro k β hβ
  have hbound :=
    lemma_17_5_2_finite_deriv_abs_le_high_temp_on_Icc_all_stages
      Λ J hJ ha hab hlt hβ_mem hxz
  have hk1 := hbound (k + 1) β hβ
  have hk := hbound k β hβ
  calc
    |deriv (fun β' =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β -
      deriv (fun β' =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β|
        ≤ |deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β| +
          |deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β| := abs_sub _ _
    _ ≤ (J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d)) +
          (J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d)) :=
        add_le_add hk1 hk
    _ = 2 * (J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 +
          J * (4 * ↑d)) := by ring

/-- **GJ §17.5 Lemma 17.5.2 uniform increment bound, self-interval form**:
the consumable specialization of
`lemma_17_5_2_finite_derivative_increment_abs_le_high_temp_on_Icc_all_stages`
in which the auxiliary parameter interval `[a, b]` is the beta interval
`[β₁, β₂]` itself.  Given that `[β₁, β₂]` lies inside the open high-temperature
region `Ioo 0 (1 / (J · 2d))`, the consecutive-stage increment `F_{k+1} - F_k`
is bounded in absolute value by `2 · (J · M² + 4dJ)` with
`M = β₂ J · 2d / (1 - β₂ J · 2d)`, uniformly in the stage `k` and the point `β`.

This is the form matching the closed-interval high-temperature data carried by
the derivative-limit provider machinery.  Part of Issue #2931. -/
theorem lemma_17_5_2_finite_derivative_increment_abs_le_high_temp_on_self_Icc
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 < J) (hd : 1 ≤ d)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ∀ k, ∀ β ∈ Set.Icc β₁ β₂,
      |deriv (fun β' =>
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β -
        deriv (fun β' =>
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β| ≤
        2 * (J * (β₂ * J * ↑(2 * d) / (1 - β₂ * J * ↑(2 * d))) ^ 2 +
          J * (4 * ↑d)) := by
  have hd_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := by omega
    exact_mod_cast this
  have hJ2d : 0 < J * ↑(2 * d) := mul_pos hJ hd_pos
  have hβ₂_lt : β₂ < 1 / (J * ↑(2 * d)) := (hIcc ⟨hβ₁₂, le_rfl⟩).2
  have hlt : β₂ * J * ↑(2 * d) < 1 := by
    have h := (lt_div_iff₀ hJ2d).1 hβ₂_lt
    calc β₂ * J * ↑(2 * d) = β₂ * (J * ↑(2 * d)) := by ring
      _ < 1 := h
  exact lemma_17_5_2_finite_derivative_increment_abs_le_high_temp_on_Icc_all_stages
    Λ J hJ.le hβ₁ hβ₁₂ hlt (fun β hβ => hβ) hxz

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider criterion, covered-stage
form**: if there is a summable sequence `c : ℕ → ℝ` such that on every closed
interval inside the open high-temperature region the consecutive-stage
finite-volume β-derivative differences are bounded by `c k` for every stage `k`
whose volume already contains the pair `{x,z}`, then the derivative-limit
provider holds.

The exhaustion eventually covers `{x,z}` (`Exhaustion.exhaust`), so all stages
beyond some onset index `N` are covered; the bound on covered stages therefore
supplies the eventual increment hypothesis of
`lemma_17_5_2_derivative_limit_provider_of_summable_increments_eventually` with
`N₀ = N`, and the finitely many head increments below `N` need no control once
the metric-Cauchy threshold is raised past `N`.  (Stages whose successor is
still uncovered contribute a zero increment, by
`lemma_17_5_2_finite_derivative_increment_eq_zero_of_not_subset`.)  This lets the
convergence-rate analysis address only the covered stages without locating the
onset index.  Part of Issue #2931. -/
theorem lemma_17_5_2_derivative_limit_provider_of_summable_increments_on_covered_stages
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (c : ℕ → ℝ) (hc : Summable c)
    (hincr :
      ∀ β₁ β₂ : ℝ,
        Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ k : ℕ, ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k →
            ∀ β ∈ Set.Icc β₁ β₂,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β) ≤ c k) :
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z := by
  obtain ⟨N, hN⟩ := Λ.exhaust ({x, z} : Finset (Fin d → ℤ))
  refine lemma_17_5_2_derivative_limit_provider_of_summable_increments_eventually
    Λ J x z c hc N (fun β₁ β₂ hIcc k hk β hβ => ?_)
  exact hincr β₁ β₂ hIcc k (hN k hk) β hβ

end Ambient
end IsingModel
