import IsingModel.ComplexAnalyticity.Basic

/-!
# Complex-parameter correlation function and its β-analyticity (Issue #3026)

Defines the complex-parameter correlation function `correlationComplex G A J h β` as
the ratio of the complex Gibbs numerator `∑_σ σ^A · exp(-β H_ℂ(σ))` to the complex
partition function, and proves it is analytic in the inverse temperature `β` wherever
the partition function is nonzero, agreeing with the real correlation on the real axis.

This supplies the complex-analytic extension required by the Cauchy-estimate derivative
bridge (`abs_deriv_le_of_complex_extension`, Issue #3026): on any β-neighborhood where
the relevant finite-volume partition functions are nonzero (in particular near the real
axis, where the real partition function is positive), the value increment
`c_k − c_{k+1}` of finite-volume correlations extends complex-analytically, so its
derivative is controlled by a complex boundary bound via Cauchy's estimate.

References:

* Glimm–Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp. 311–312.
-/

namespace IsingModel

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Complex spin product `σ^A = ∏_{i ∈ A} toSign(σ_i)`, valued in `ℂ`. -/
noncomputable def spinProductComplex (A : Finset ι) (σ : Config ι) : ℂ :=
  ∏ i ∈ A, ((σ i).toSign : ℂ)

omit [Fintype ι] [DecidableEq ι] in
/-- `Complex.ofReal (spinProduct A σ) = spinProductComplex A σ`. -/
theorem spinProduct_ofReal_eq_spinProductComplex (A : Finset ι) (σ : Config ι) :
    ((spinProduct A σ : ℝ) : ℂ) = spinProductComplex A σ := by
  unfold spinProduct spinProductComplex
  push_cast
  rfl

/-- Complex-parameter Gibbs numerator for the observable `σ^A`:
`N(J, h, β) = ∑_σ σ^A · exp(-β · H(σ; J, h))`. -/
noncomputable def gibbsNumeratorComplex (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (J h β : ℂ) : ℂ :=
  ∑ σ : Config ι, spinProductComplex A σ * Complex.exp (-β * hamiltonianComplex G J h σ)

/-- Complex-parameter correlation function:
`⟨σ^A⟩(J, h, β) = N(J, h, β) / Z(J, h, β)`. -/
noncomputable def correlationComplex (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (J h β : ℂ) : ℂ :=
  (partitionFunctionComplex G J h β)⁻¹ * gibbsNumeratorComplex G A J h β

/-- `gibbsNumeratorComplex` is entire in the inverse temperature `β`: a finite sum of
`σ^A`-weighted exponentials, with `σ^A` constant in `β`. -/
theorem gibbsNumeratorComplex_analyticAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet] (A : Finset ι) (J h : ℂ) (β₀ : ℂ) :
    AnalyticAt ℂ (fun β => gibbsNumeratorComplex G A J h β) β₀ := by
  unfold gibbsNumeratorComplex hamiltonianComplex externalFieldEnergyComplex
    interactionEnergyComplex
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine analyticAt_const.mul (AnalyticAt.cexp' ?_)
  fun_prop

/-- `correlationComplex` is analytic in `β` wherever the complex partition function is
nonzero: the ratio of the entire numerator and the entire (nonzero) partition function.
-/
theorem correlationComplex_analyticAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet] (A : Finset ι) (J h : ℂ) (β₀ : ℂ)
    (hZ : partitionFunctionComplex G J h β₀ ≠ 0) :
    AnalyticAt ℂ (fun β => correlationComplex G A J h β) β₀ := by
  unfold correlationComplex
  exact ((partitionFunctionComplex_analyticAt_beta G J h β₀).inv hZ).mul
    (gibbsNumeratorComplex_analyticAt_beta G A J h β₀)

/-- `Complex.ofReal (∑_σ σ^A · boltzmannWeight) = gibbsNumeratorComplex` at real
parameters. Mirrors `partitionFunction_ofReal_eq_partitionFunctionComplex`. -/
theorem gibbsNumerator_ofReal_eq_gibbsNumeratorComplex
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) (A : Finset ι) :
    ((∑ σ : Config ι, spinProduct A σ * boltzmannWeight G p σ : ℝ) : ℂ)
      = gibbsNumeratorComplex G A (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) := by
  unfold gibbsNumeratorComplex boltzmannWeight hamiltonianComplex
    externalFieldEnergyComplex interactionEnergyComplex
    hamiltonian interactionEnergy externalFieldEnergy
  push_cast
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [spinProduct_ofReal_eq_spinProductComplex]
  congr 1
  have hspin : ∀ i : ι, ((Spin.sign ℝ (σ i) : ℝ) : ℂ) = Spin.sign ℂ (σ i) := by
    intro i; simp [Spin.sign]
  have hedge : ∀ e : Sym2 ι,
      ((edgeSpin (K := ℝ) σ e : ℝ) : ℂ) = edgeSpinComplex σ e :=
    edgeSpin_ofReal_eq_edgeSpinComplex σ
  push_cast [← hspin, ← hedge]
  ring

/-- `Complex.ofReal (correlation G p A) = correlationComplex G p.J p.h p.β` at real
parameters: the complex correlation extends the real correlation along the real axis. -/
theorem correlation_ofReal_eq_correlationComplex
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) (A : Finset ι) :
    ((correlation G p A : ℝ) : ℂ)
      = correlationComplex G A (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) := by
  unfold correlation gibbsExpectation correlationComplex
  rw [Complex.ofReal_mul, Complex.ofReal_inv,
    partitionFunction_ofReal_eq_partitionFunctionComplex G p,
    gibbsNumerator_ofReal_eq_gibbsNumeratorComplex G p A]

end IsingModel
