import IsingModel.ComplexAnalyticity.Basic
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

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

open Metric in
/-- **`correlationComplex` is `DiffContOnCl` on a disc where the partition function is
nonvanishing** (Issue #3026). If the complex partition function is nonzero on the closed
disc `closedBall β₀ R` (`R > 0`), then `correlationComplex` is differentiable on the open
disc and continuous up to the boundary, i.e. `DiffContOnCl ℂ · (ball β₀ R)` — the exact
hypothesis of the Cauchy-estimate derivative bridge `abs_deriv_le_of_complex_extension`.
Follows from `correlationComplex_analyticAt_beta` at each point of the closed disc and
`DifferentiableOn.diffContOnCl` (`closure (ball) = closedBall`). -/
theorem correlationComplex_diffContOnCl_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (J h : ℂ) (β₀ : ℂ) {R : ℝ} (hR : 0 < R)
    (hZ : ∀ z ∈ closedBall β₀ R, partitionFunctionComplex G J h z ≠ 0) :
    DiffContOnCl ℂ (fun β => correlationComplex G A J h β) (ball β₀ R) := by
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball β₀ (ne_of_gt hR)]
  intro z hz
  exact (correlationComplex_analyticAt_beta G A J h z (hZ z hz)).differentiableAt
    |>.differentiableWithinAt

open Metric in
/-- **`correlationComplex` is `DiffContOnCl` on a small disc centered at a real
inverse temperature** (Issue #3026). At real parameters `p : IsingParams ℝ` the complex
partition function at `↑p.β` equals `↑(partitionFunction G p) ≠ 0`; by continuity it is
nonvanishing on a small closed disc, so `correlationComplex` is `DiffContOnCl` there.
This produces a concrete disc on which the Cauchy-estimate derivative bridge applies. -/
theorem correlationComplex_diffContOnCl_beta_of_real (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (p : IsingParams ℝ) :
    ∃ R > 0, DiffContOnCl ℂ (fun β => correlationComplex G A (p.J : ℂ) (p.h : ℂ) β)
      (ball (p.β : ℂ) R) := by
  have hZ0 : partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) ≠ 0 := by
    rw [← partitionFunction_ofReal_eq_partitionFunctionComplex G p]
    exact Complex.ofReal_ne_zero.mpr (partitionFunction_ne_zero G p)
  have hcont : ContinuousAt (fun β => partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) β)
      (p.β : ℂ) :=
    (partitionFunctionComplex_analyticAt_beta G (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)).continuousAt
  have hev : ∀ᶠ z in nhds (p.β : ℂ), partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) z ≠ 0 :=
    hcont.eventually_ne hZ0
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp hev
  exact ⟨R, hR, correlationComplex_diffContOnCl_beta G A (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) hR hball⟩

omit [DecidableEq ι] in
/-- **Complex Hamiltonian at real parameters is the real-cast of the real Hamiltonian**
(Issue #3044, foundational complex/real cast). For real `J, h` and any spin
configuration, the complex Hamiltonian coincides with `ℝ → ℂ` of the real one. -/
theorem hamiltonianComplex_ofReal_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (σ : Config ι) :
    hamiltonianComplex G (p.J : ℂ) (p.h : ℂ) σ = ((hamiltonian G p σ : ℝ) : ℂ) := by
  unfold hamiltonianComplex hamiltonian interactionEnergyComplex interactionEnergy
    externalFieldEnergyComplex externalFieldEnergy
  push_cast
  have hspin : ∀ i : ι, ((Spin.sign ℝ (σ i) : ℝ) : ℂ) = Spin.sign ℂ (σ i) := by
    intro i; simp [Spin.sign]
  have hedge : ∀ e : Sym2 ι,
      ((edgeSpin (K := ℝ) σ e : ℝ) : ℂ) = edgeSpinComplex σ e :=
    edgeSpin_ofReal_eq_edgeSpinComplex σ
  push_cast [← hspin, ← hedge]
  ring

omit [DecidableEq ι] in
/-- **Modulus of a complex Boltzmann weight at real parameters** (Issue #3044): for any
complex inverse temperature `β` and real parameters `J, h`,
`‖exp(-β · H_ℂ(σ))‖ = exp(-β.re · H_ℝ(σ))`, where `H_ℂ = hamiltonianComplex G ↑J ↑h` is
the real-cast of the real Hamiltonian. This is the foundational identity behind the
complex partition-function and correlation modulus bounds. -/
theorem norm_exp_neg_beta_hamiltonianComplex (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (β : ℂ) (σ : Config ι) :
    ‖Complex.exp (-β * hamiltonianComplex G (p.J : ℂ) (p.h : ℂ) σ)‖
      = Real.exp (-β.re * hamiltonian G p σ) := by
  rw [hamiltonianComplex_ofReal_eq G p σ, Complex.norm_exp]
  simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-- **Norm bound for the complex partition function at real parameters** (Issue #3044):
for real `J, h` and complex `β`, `‖Z_ℂ(β)‖ ≤ Z_ℝ(β.re)` — the modulus of the complex
partition function is dominated by the real partition function at the real part of `β`.
Sum-of-moduli + `norm_exp_neg_beta_hamiltonianComplex`. -/
theorem partitionFunctionComplex_norm_le_real (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (β : ℂ) :
    ‖partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) β‖
      ≤ partitionFunction G (⟨p.J, p.h, β.re⟩ : IsingParams ℝ) := by
  unfold partitionFunctionComplex partitionFunction boltzmannWeight
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun σ _ => ?_)
  rw [norm_exp_neg_beta_hamiltonianComplex G p β σ]
  exact le_refl _

/-- **Norm bound for the complex Gibbs numerator at real parameters** (Issue #3044): for
real `J, h` and complex `β`,
`‖∑_σ σ^A · exp(-β H_ℂ(σ))‖ ≤ Z_ℝ(β.re)`, since `|σ^A| = 1` (spin product) and each
Boltzmann modulus is dominated by the real value. -/
theorem gibbsNumeratorComplex_norm_le_real (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (p : IsingParams ℝ) (β : ℂ) :
    ‖gibbsNumeratorComplex G A (p.J : ℂ) (p.h : ℂ) β‖
      ≤ partitionFunction G (⟨p.J, p.h, β.re⟩ : IsingParams ℝ) := by
  unfold gibbsNumeratorComplex partitionFunction boltzmannWeight
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun σ _ => ?_)
  rw [norm_mul, norm_exp_neg_beta_hamiltonianComplex G p β σ]
  -- ‖spinProductComplex A σ‖ * exp(-β.re * H_ℝ σ) ≤ exp(-β.re * H_ℝ σ); needs ‖spinProduct‖ ≤ 1
  have hspin_norm : ‖spinProductComplex A σ‖ ≤ 1 := by
    unfold spinProductComplex
    rw [norm_prod]
    refine Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => ?_)
    rcases σ i with hp | hn
    · simp [Spin.toSign]
    · simp [Spin.toSign]
  have hexp_nn : 0 ≤ Real.exp (-β.re * hamiltonian G p σ) := (Real.exp_pos _).le
  exact (mul_le_of_le_one_left hexp_nn hspin_norm)

/-- **Norm bound for the complex correlation at real parameters** (Issue #3044): for real
`J, h` and complex `β` with `Z_ℂ(β) ≠ 0`,
`‖⟨σ^A⟩_ℂ(β)‖ ≤ Z_ℝ(β.re) / ‖Z_ℂ(β)‖`, the modulus of the complex correlation is bounded
by the ratio of the real partition function at `β.re` to the modulus of the complex
partition function at `β`. The denominator's volume-uniform lower bound (cluster
expansion / Lee-Yang) is the genuine remaining input. -/
theorem correlationComplex_norm_le_ratio (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (p : IsingParams ℝ) (β : ℂ) :
    ‖correlationComplex G A (p.J : ℂ) (p.h : ℂ) β‖
      ≤ partitionFunction G (⟨p.J, p.h, β.re⟩ : IsingParams ℝ)
        / ‖partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) β‖ := by
  unfold correlationComplex
  rw [norm_mul, norm_inv]
  rw [div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left (gibbsNumeratorComplex_norm_le_real G A p β) ?_
  exact inv_nonneg.mpr (norm_nonneg _)

/-- **Norm of the complex partition function is at least its real part** (Issue #3044):
trivially `Re(Z_ℂ(β)) ≤ ‖Z_ℂ(β)‖` (`Complex.re_le_norm`). Combined with the explicit real
part formula `partitionFunctionComplex_re_eq`, this is the standard lower-bound entry
point for the volume-uniform `‖Z_ℂ‖` estimate underlying the complex Simon-Lieb. -/
theorem partitionFunctionComplex_re_le_norm (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (β : ℂ) :
    (partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) β).re
      ≤ ‖partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) β‖ :=
  Complex.re_le_norm _

/-- **Explicit real-part formula for the complex partition function at real parameters**
(Issue #3044): for real `J, h` and complex `β`, the real part of `Z_ℂ(β)` is the
weighted cosine sum
`Re(Z_ℂ(β)) = ∑_σ exp(-β.re · H_ℝ(σ)) · cos(β.im · H_ℝ(σ))`.
Follows from `Complex.exp_re` applied to each summand
`exp(-β · H_ℂ(σ)) = exp(-β · ↑H_ℝ(σ))` together with `Real.cos_neg`. This is the entry
point for the lower bound `‖Z_ℂ‖ ≥ Z_ℝ(β.re) − (cosine deficit)`. -/
theorem partitionFunctionComplex_re_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (β : ℂ) :
    (partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) β).re
      = ∑ σ : Config ι, Real.exp (-β.re * hamiltonian G p σ) *
          Real.cos (β.im * hamiltonian G p σ) := by
  unfold partitionFunctionComplex
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hamiltonianComplex_ofReal_eq G p σ, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Real.cos_neg]

/-- **Quantitative cosine-deficit lower bound for `Re(Z_ℂ)`** (Issue #3044): for real
parameters `J, h` and complex `β`,
`Re(Z_ℂ(β)) ≥ Z_ℝ(β.re) − (β.im)²/2 · ∑_σ exp(-β.re · H_ℝ(σ)) · (H_ℝ(σ))²`.

Applies the cosine lower bound `Real.one_sub_sq_div_two_le_cos`
(`1 − x²/2 ≤ cos x`) per-σ inside the cosine sum
`Re(Z_ℂ) = ∑_σ exp(-β.re · H_ℝ) · cos(β.im · H_ℝ)` and rewrites the resulting Boltzmann-
weighted second-moment sum as `(β.im)²/2 · ∑_σ exp · H²`. Combined with
`re_le_norm`, gives the lower bound
`‖Z_ℂ(β)‖ ≥ Z_ℝ(β.re) − (β.im)²/2 · ∑_σ exp(-β.re · H_ℝ) · H_ℝ²`.

The deficit is volume-dependent through the second-moment sum (extensive `H_ℝ`), giving
a non-uniform disc radius; the volume-uniform refinement requires cluster-expansion
control on the second moment (the remaining Lee-Yang / Mayer ingredient). -/
theorem partitionFunctionComplex_re_ge_deficit (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (β : ℂ) :
    partitionFunction G (⟨p.J, p.h, β.re⟩ : IsingParams ℝ)
        - β.im ^ 2 / 2 *
          (∑ σ : Config ι, Real.exp (-β.re * hamiltonian G p σ) * hamiltonian G p σ ^ 2)
      ≤ (partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) β).re := by
  rw [partitionFunctionComplex_re_eq]
  have hPF : partitionFunction G (⟨p.J, p.h, β.re⟩ : IsingParams ℝ)
      = ∑ σ : Config ι, Real.exp (-β.re * hamiltonian G p σ) := by
    unfold partitionFunction boltzmannWeight; rfl
  rw [hPF, show β.im ^ 2 / 2 *
        (∑ σ : Config ι, Real.exp (-β.re * hamiltonian G p σ) * hamiltonian G p σ ^ 2)
      = ∑ σ : Config ι, Real.exp (-β.re * hamiltonian G p σ) *
          (β.im * hamiltonian G p σ) ^ 2 / 2 from by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun σ _ => by ring]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun σ _ => ?_)
  rw [show Real.exp (-β.re * hamiltonian G p σ)
        - Real.exp (-β.re * hamiltonian G p σ) * (β.im * hamiltonian G p σ) ^ 2 / 2
      = Real.exp (-β.re * hamiltonian G p σ) *
          (1 - (β.im * hamiltonian G p σ) ^ 2 / 2) from by ring]
  exact mul_le_mul_of_nonneg_left Real.one_sub_sq_div_two_le_cos (Real.exp_pos _).le

end IsingModel
