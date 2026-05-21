import IsingModel.ComplexAnalyticity.Vitali

/-!
# Complex Free-Energy Bounds

This module is part of the split `IsingModel.ComplexAnalyticity` development.
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Complex

/-- **Modulus bound for `partitionFunctionComplex` via the real Ising
partition function (statement, proof deferred)**. For real `β`, real `J`,
complex `h`:
`|Z(J, h, β)| ≤ Z(J, Re h, β)` (as the real Ising partition function).

Proof idea: `|exp(-β·H(σ))| = exp(Re(-β·H(σ)))`; the real part of the
complex exponent is exactly the real Boltzmann exponent at parameters
`⟨J, Re h, β⟩`. Summing gives the stated bound.

This estimate feeds into the boundedness input for the ∞-vol Vitali
lift (combined with the uniform upper bound on the real partition
function via `Fintype.card_pos`). -/
theorem norm_partitionFunctionComplex_le_partitionFunction
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J : ℝ) (h : ℂ) :
    ‖partitionFunctionComplex G (J : ℂ) h (β : ℂ)‖
      ≤ partitionFunction G ⟨J, h.re, β⟩ := by
  classical
  unfold partitionFunctionComplex partitionFunction boltzmannWeight
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun σ _ => ?_)
  rw [Complex.norm_exp]
  -- Show the real-part of the complex exponent equals the real exponent.
  have hexp_eq :
      (-(β : ℂ) * hamiltonianComplex G (J : ℂ) h σ).re
        = -β * hamiltonian G ⟨J, h.re, β⟩ σ := by
    unfold hamiltonianComplex interactionEnergyComplex
      externalFieldEnergyComplex
    unfold hamiltonian interactionEnergy externalFieldEnergy
    -- Step 1: ∑ edgeSpinComplex σ e has real part = ∑ edgeSpin σ e (all real).
    have hEdge : (∑ e ∈ G.edgeFinset, edgeSpinComplex σ e).re
                  = ∑ e ∈ G.edgeFinset, edgeSpin σ e := by
      simp only [Complex.re_sum]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      refine Sym2.ind (fun i j => ?_) e
      unfold edgeSpinComplex edgeSpin
      rw [Sym2.lift_mk, Sym2.lift_mk]
      cases σ i <;> cases σ j <;>
        simp [Spin.sign, Spin.toSign]
    -- Step 2: ∑ Spin.sign ℂ real part = ∑ Spin.sign ℝ.
    have hSpin : (∑ i : ι, Spin.sign ℂ (σ i)).re
                  = ∑ i : ι, Spin.sign ℝ (σ i) := by
      simp only [Complex.re_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      cases σ i <;> simp [Spin.sign, Spin.toSign]
    -- Step 3: compute the full expression.
    have him_sum : (∑ i : ι, Spin.sign ℂ (σ i)).im = 0 := by
      simp only [Complex.im_sum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      cases σ i <;> simp [Spin.sign, Spin.toSign]
    simp [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re,
      hEdge, hSpin, him_sum]
  rw [hexp_eq]

/-- **Explicit trivial upper bound on `|partitionFunctionComplex|`**
combining `norm_partitionFunctionComplex_le_partitionFunction` with
`partitionFunction_upper`: for real `β, J` and complex `h`,
`|Z(J, h, β)| ≤ 2^|ι| · exp(|β|·(|J|·|E| + |Re h|·|ι|))`.

This gives a locally uniform bound on `|Z|` over compact subsets of
`ℂ` where `|Re h|` is bounded, which is the input for Montel's theorem
in the ∞-vol Vitali lift. -/
theorem norm_partitionFunctionComplex_le_trivial_bound
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J : ℝ) (h : ℂ) :
    ‖partitionFunctionComplex G (J : ℂ) h (β : ℂ)‖
      ≤ Fintype.card (Config ι)
        * Real.exp (|β| * (|J| * G.edgeFinset.card + |h.re| * Fintype.card ι)) := by
  refine (norm_partitionFunctionComplex_le_partitionFunction G β J h).trans ?_
  exact partitionFunction_upper G ⟨J, h.re, β⟩

/-- **Simple norm bound for `Complex.log`**: `‖log z‖ ≤ |log ‖z‖| + π`.
Direct from `log_re = log |z|`, `|log_im| = |arg z| ≤ π`, and the
triangle inequality on the real/imaginary parts. -/
theorem norm_complex_log_le (z : ℂ) :
    ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
  have h_re : (Complex.log z).re = Real.log ‖z‖ := Complex.log_re z
  have h_im_abs : |(Complex.log z).im| ≤ Real.pi := by
    rw [Complex.log_im]
    exact abs_le.mpr ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
  calc ‖Complex.log z‖
      ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ |Real.log ‖z‖| + Real.pi := by rw [h_re]; linarith [h_im_abs]

/-- **Principal complex free-energy log-norm bound** for `[Nonempty ι]`:
`‖f(J, h, β)‖ ≤ |log ‖Z_ℂ(J,h,β)‖| / |ι| + π/|ι|`. This follows from
`norm_complex_log_le` and records the exact normalised absolute-log input
needed for later infinite-volume bounds. A separate lower control on
`‖Z_ℂ‖` is needed before this becomes a Montel-style uniform bound. -/
theorem norm_freeEnergyComplex_le_trivial_bound
    (G : SimpleGraph ι) [Fintype G.edgeSet] [Nonempty ι]
    (β J : ℝ) (h : ℂ) :
    ‖freeEnergyComplex G (J : ℂ) h (β : ℂ)‖
      ≤ |Real.log ‖partitionFunctionComplex G (J : ℂ) h (β : ℂ)‖|
          / (Fintype.card ι : ℝ) + Real.pi / (Fintype.card ι : ℝ) := by
  classical
  unfold freeEnergyComplex
  have hNℕ : 0 < Fintype.card ι := Fintype.card_pos
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hNℕ.ne'
  rw [norm_mul, norm_inv]
  have h_log : ‖Complex.log (partitionFunctionComplex G (J : ℂ) h (β : ℂ))‖
              ≤ |Real.log ‖partitionFunctionComplex G (J : ℂ) h (β : ℂ)‖|
                  + Real.pi :=
    norm_complex_log_le _
  have hN_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hNℕ
  have hNorm : ‖((Fintype.card ι : ℂ) : ℂ)‖ = (Fintype.card ι : ℝ) := by
    simp
  rw [hNorm]
  have := mul_le_mul_of_nonneg_left h_log
    (show (0 : ℝ) ≤ (Fintype.card ι : ℝ)⁻¹ from inv_nonneg.mpr hN_pos.le)
  calc (Fintype.card ι : ℝ)⁻¹ *
        ‖Complex.log (partitionFunctionComplex G (J : ℂ) h (β : ℂ))‖
      ≤ (Fintype.card ι : ℝ)⁻¹ *
          (|Real.log ‖partitionFunctionComplex G (J : ℂ) h (β : ℂ)‖|
            + Real.pi) := this
    _ = _ := by field_simp

/-- **`freeEnergyComplex` is DifferentiableOn on `leeYangSubdomain`**
(consequence of subdomain analyticity). Useful as input to Vitali for
restricted subdomains. -/
theorem freeEnergyComplex_differentiableOn_leeYangSubdomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    DifferentiableOn ℂ (fun h' => freeEnergyComplex G (J : ℂ) h' (β : ℂ))
        (leeYangSubdomain β (Fintype.card ι)) := fun _ hmem =>
  (freeEnergyComplex_analyticAt_h_of_leeYangSubdomain
      G hβ J hmem.2).differentiableAt.differentiableWithinAt

/-- **Vitali bridge on `leeYangSubdomain`**: locally uniform limit on
the subdomain of DifferentiableOn-complex-analytic functions is again
DifferentiableOn. Specialisation of `vitali_bridge` to
`U = leeYangSubdomain β N`. -/
theorem vitali_bridge_leeYangSubdomain
    (β : ℝ) (N : ℕ)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) (leeYangSubdomain β N))
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop
      (leeYangSubdomain β N)) :
    DifferentiableOn ℂ f (leeYangSubdomain β N) :=
  vitali_bridge (isOpen_leeYangSubdomain β N) hF hconv

/-- **Vitali bridge via `AnalyticOnNhd` / `Filter.Eventually`**.
A more flexible version of `vitali_bridge` allowing the holomorphicity
hypothesis to hold only eventually along the filter. Needed for
sequences of finite-volume free energies indexed by an exhaustion
`Λ : ℕ → Finset V` — the `DifferentiableOn` hypothesis on `F n`
holds for all `n`, so the eventually-version is a trivial
generalisation that matches mathlib's signature directly. -/
theorem vitali_bridge_eventually {U : Set ℂ} (hU : IsOpen U)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ᶠ n in Filter.atTop, DifferentiableOn ℂ (F n) U)
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop U) :
    DifferentiableOn ℂ f U :=
  hconv.differentiableOn hF hU

/-- **`freeEnergyComplex` coincides with real `freeEnergy` on `ℝ`**
(cast to `ℂ`). Rewrite of `freeEnergy_ofReal_eq_freeEnergyComplex`
in the form most useful for Vitali (pointwise convergence on the
real axis via Fekete's theorem). -/
theorem freeEnergyComplex_ofReal_eq_freeEnergy
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) :
    freeEnergyComplex G (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)
      = ((freeEnergy G p : ℝ) : ℂ) :=
  (freeEnergy_ofReal_eq_freeEnergyComplex G p).symm

/-- **Uniform-on-compacts norm bound on `partitionFunctionComplex`**:
for real `β, J`, the map `h ↦ ‖Z(J, h, β)‖` is bounded on any bounded
subset of `ℂ`. Concretely, if `|Re h| ≤ R` then
`‖Z‖ ≤ 2^|ι| · exp(|β|·(|J|·|E| + R·|ι|))`. -/
theorem norm_partitionFunctionComplex_le_of_re_bound
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J : ℝ) {R : ℝ} {h : ℂ} (hh : |h.re| ≤ R) :
    ‖partitionFunctionComplex G (J : ℂ) h (β : ℂ)‖
      ≤ Fintype.card (Config ι)
        * Real.exp (|β| * (|J| * G.edgeFinset.card + R * Fintype.card ι)) := by
  refine (norm_partitionFunctionComplex_le_trivial_bound G β J h).trans ?_
  gcongr

/-- `partitionFunctionComplex` is non-zero at every point of
`leeYangSubdomain` (which is contained in `leeYangDomain` where
non-vanishing is already established). -/
theorem partitionFunctionComplex_ne_zero_on_leeYangSubdomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) {h : ℂ}
    (hh : h ∈ leeYangSubdomain β (Fintype.card ι)) :
    partitionFunctionComplex G (J : ℂ) h (β : ℂ) ≠ 0 :=
  partitionFunctionComplex_ne_zero_on_leeYangDomain G hβ hJ
    (leeYangSubdomain_subset_leeYangDomain β (Fintype.card ι) hh)

/-- Specialisation to the real-positive basepoint: the point `(h₀ : ℂ)`
for real `h₀ > 0` is in `leeYangSubdomain β N` for any `β, N` (since
`|Im| = 0` makes both conjuncts trivial). -/
theorem real_pos_mem_leeYangSubdomain
    (β : ℝ) (N : ℕ) {h₀ : ℝ} (hpos : 0 < h₀) :
    (h₀ : ℂ) ∈ leeYangSubdomain β N := by
  refine ⟨?_, ?_⟩
  · simp [hpos]
  · have him : (h₀ : ℂ).im = 0 := by simp
    rw [him, abs_zero, mul_zero, zero_mul]
    positivity

end IsingModel
