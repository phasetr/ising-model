import IsingModel.ComplexAnalyticity.Factorization

/-!
# Lee-Yang Subdomain Analyticity

This module is part of the split `IsingModel.ComplexAnalyticity` development.
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Complex

/-! ### slitPlane via `Re Z > 0` on a Lee-Yang subdomain (PR #200 in progress)

Toward GJ §4.6 Thm 4.6.2 finite-volume analyticity on the Lee-Yang
domain: we establish `partitionFunctionComplex ∈ Complex.slitPlane`
by the stronger `Re Z > 0` condition, which holds on the subdomain
`{h | |Im h| < Re h ∧ β · |Im h| · |ι| < π/2}`.

The bound `β · |Im h| · |ι| < π/2` ensures that for any configuration
`σ` with spin sum `s ∈ [-|ι|, |ι|]`, `|β · Im h · s| < π/2`, hence
`cos(β · Im h · s) > 0`. The real part of each Boltzmann weight is
then `exp(β·J·(edge sum) + β·Re h · s) · cos(β · Im h · s) > 0`, and
summing over `σ` gives `Re Z > 0`.

This is a strictly weaker statement than the full Lee-Yang analyticity,
but it is a concrete subdomain where the finite-volume complex
analyticity of `freeEnergyComplex` holds without a separate branch
construction.

Full Lee-Yang extension requires a continuous branch argument on the
simply-connected domain (classical complex analysis; not directly
available as a mathlib lemma at present). -/

/-- The restricted Lee-Yang subdomain on which we prove `Re Z > 0`:
`{h | |Im h| < Re h ∧ β · |Im h| · |ι| < π/2}`. This domain shrinks
as `β · |ι|` grows, so it does not lift to the infinite-volume limit;
the full Lee-Yang domain requires a branch argument. -/
def leeYangSubdomain (β : ℝ) (N : ℕ) : Set ℂ :=
  {h : ℂ | |h.im| < h.re ∧ β * |h.im| * (N : ℝ) < Real.pi / 2}

/-- `leeYangSubdomain ⊆ leeYangDomain` by the first conjunct. -/
theorem leeYangSubdomain_subset_leeYangDomain (β : ℝ) (N : ℕ) :
    leeYangSubdomain β N ⊆ leeYangDomain := fun _ hh => hh.1

/-- The Lee-Yang subdomain is open: intersection of two open sets defined
by strict inequalities on continuous functions. -/
theorem isOpen_leeYangSubdomain (β : ℝ) (N : ℕ) :
    IsOpen (leeYangSubdomain β N) := by
  have h₁ : IsOpen {h : ℂ | |h.im| < h.re} := isOpen_leeYangDomain
  have h₂ : IsOpen {h : ℂ | β * |h.im| * (N : ℝ) < Real.pi / 2} := by
    have hcont : Continuous (fun h : ℂ => β * |h.im| * (N : ℝ)) := by
      fun_prop
    exact hcont.isOpen_preimage _ isOpen_Iio
  exact h₁.inter h₂

omit [DecidableEq ι] in
/-- The spin sum `∑ σ_i` has absolute value at most `|ι|`, since each
`σ_i ∈ {-1, 1}`. -/
theorem abs_spinSum_le (σ : Config ι) :
    |∑ i : ι, (Spin.sign ℝ (σ i) : ℝ)| ≤ (Fintype.card ι : ℝ) := by
  classical
  have h₁ : |∑ i : ι, Spin.sign ℝ (σ i)|
              ≤ ∑ i : ι, |Spin.sign ℝ (σ i)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h₂ : ∀ i : ι, |Spin.sign ℝ (σ i)| ≤ 1 := by
    intro i; cases σ i <;> simp [Spin.sign, Spin.toSign]
  have h₃ : ∑ i : ι, |Spin.sign ℝ (σ i)| ≤ ∑ _i : ι, (1 : ℝ) :=
    Finset.sum_le_sum (fun i _ => h₂ i)
  simpa [Finset.sum_const, Finset.card_univ] using h₁.trans h₃

omit [DecidableEq ι] in
/-- **Per-configuration Boltzmann weight has positive real part** on
`leeYangSubdomain`. Real parameters `β > 0`, real `J`; complex uniform
field `h` with `β · |Im h| · |ι| < π/2`. The exponential factors as
`exp(β·J·(edge sum) + β·Re h · s) · (cos(β·Im h · s) + i sin(β·Im h · s))`
with `s = spin sum`, and `|β·Im h · s| ≤ β · |Im h| · |ι| < π/2`
forces `cos > 0`. -/
theorem exp_neg_beta_hamiltonian_re_pos
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (himπ : β * |h.im| * (Fintype.card ι : ℝ) < Real.pi / 2)
    (σ : Config ι) :
    0 < (Complex.exp (-(β : ℂ) * hamiltonianComplex G (J : ℂ) h σ)).re := by
  classical
  -- Reduce to an explicit real-imag decomposition.
  unfold hamiltonianComplex interactionEnergyComplex externalFieldEnergyComplex
  set e : ℝ := ∑ ed ∈ G.edgeFinset,
      (Spin.sign ℝ (σ (Quot.out ed).1) * Spin.sign ℝ (σ (Quot.out ed).2))
    with he_def
  set s : ℝ := ∑ i : ι, (Spin.sign ℝ (σ i) : ℝ) with hs_def
  have hedgeCast : (∑ ed ∈ G.edgeFinset, edgeSpinComplex σ ed) = (e : ℂ) := by
    simp only [he_def, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun ed _ => ?_)
    rw [edgeSpinComplex_eq_quotOut σ ed]
    cases σ (Quot.out ed).1 <;> cases σ (Quot.out ed).2 <;>
      simp [Spin.sign, Spin.toSign]
  have hsumCast : (∑ i : ι, Spin.sign ℂ (σ i)) = (s : ℂ) := by
    simp only [hs_def, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    cases σ i <;> simp [Spin.sign, Spin.toSign]
  rw [hedgeCast, hsumCast]
  -- The exponent is (β·J·e + β·Re h · s) + i·β·Im h · s (as a complex).
  set a : ℝ := β * J * e + β * h.re * s with ha_def
  set b : ℝ := β * h.im * s with hb_def
  have hexpCast : -(β : ℂ) * (-(J : ℂ) * (e : ℂ) + -h * (s : ℂ))
                  = (a : ℂ) + (b : ℂ) * Complex.I := by
    simp only [ha_def, hb_def]
    have hhre : (h.re : ℂ) + h.im * Complex.I = h := by
      exact (Complex.re_add_im h)
    have : -(β : ℂ) * (-(J : ℂ) * (e : ℂ) + -h * (s : ℂ))
             = ((β : ℂ) * (J : ℂ) * (e : ℂ)
                + (β : ℂ) * ((h.re : ℂ) + h.im * Complex.I) * (s : ℂ)) := by
      rw [hhre]; ring
    rw [this]; push_cast; ring
  rw [hexpCast]
  -- Now Re(exp(a + ib)) = exp(a) · cos(b) > 0 since cos(b) > 0 for |b|<π/2.
  rw [show (a : ℂ) + (b : ℂ) * Complex.I = ((⟨a, b⟩ : ℂ)) from by
    apply Complex.ext <;> simp]
  have hbRe : (⟨a, b⟩ : ℂ).re = a := rfl
  have hbIm : (⟨a, b⟩ : ℂ).im = b := rfl
  rw [Complex.exp_re, hbRe, hbIm]
  -- Need: exp(a) · cos(b) > 0.
  have habs : |b| ≤ β * |h.im| * (Fintype.card ι : ℝ) := by
    have : |b| = β * |h.im| * |s| := by
      simp only [hb_def]
      rw [abs_mul, abs_mul, abs_of_pos hβ]
    rw [this]
    have hsle : |s| ≤ (Fintype.card ι : ℝ) := abs_spinSum_le σ
    have hmul_nn : 0 ≤ β * |h.im| := mul_nonneg hβ.le (abs_nonneg _)
    exact (mul_le_mul_of_nonneg_left hsle hmul_nn)
  have hb_lt : |b| < Real.pi / 2 := lt_of_le_of_lt habs himπ
  have hcos_pos : 0 < Real.cos b := by
    rcases abs_lt.mp hb_lt with ⟨h₁, h₂⟩
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, h₂⟩
  have hexp_pos : 0 < Real.exp a := Real.exp_pos _
  exact mul_pos hexp_pos hcos_pos

/-- **`Re(partitionFunctionComplex) > 0` on the Lee-Yang subdomain**.
Sum of per-σ positive-real-part Boltzmann weights. -/
theorem partitionFunctionComplex_re_pos_of_leeYangSubdomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (himπ : β * |h.im| * (Fintype.card ι : ℝ) < Real.pi / 2) :
    0 < (partitionFunctionComplex G (J : ℂ) h (β : ℂ)).re := by
  classical
  unfold partitionFunctionComplex
  rw [show ((∑ σ : Config ι,
            Complex.exp (-(β : ℂ) * hamiltonianComplex G (J : ℂ) h σ))).re
          = ∑ σ : Config ι,
            (Complex.exp (-(β : ℂ) * hamiltonianComplex G (J : ℂ) h σ)).re
          from by rw [Complex.re_sum]]
  refine Finset.sum_pos (fun σ _ =>
    exp_neg_beta_hamiltonian_re_pos G hβ J himπ σ) ?_
  exact ⟨Classical.arbitrary (Config ι), Finset.mem_univ _⟩

/-- **`partitionFunctionComplex ∈ Complex.slitPlane` on the Lee-Yang
subdomain**: `Re Z > 0` implies slitPlane. -/
theorem partitionFunctionComplex_mem_slitPlane_of_leeYangSubdomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (himπ : β * |h.im| * (Fintype.card ι : ℝ) < Real.pi / 2) :
    partitionFunctionComplex G (J : ℂ) h (β : ℂ) ∈ Complex.slitPlane :=
  Or.inl (partitionFunctionComplex_re_pos_of_leeYangSubdomain G hβ J himπ)

/-- **`freeEnergyComplex` is analytic in `h` on the Lee-Yang subdomain**
(finite-volume `freeEnergyComplex` analyticity; GJ §4.6 Thm 4.6.2
partial — subdomain where `β · |Im h| · |ι| < π/2`, which collapses as
`|ι| → ∞`). Combines
`partitionFunctionComplex_mem_slitPlane_of_leeYangSubdomain` with
`freeEnergyComplex_analyticAt_h`. -/
theorem freeEnergyComplex_analyticAt_h_of_leeYangSubdomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (himπ : β * |h.im| * (Fintype.card ι : ℝ) < Real.pi / 2) :
    AnalyticAt ℂ (fun h' => freeEnergyComplex G (J : ℂ) h' (β : ℂ)) h :=
  freeEnergyComplex_analyticAt_h G (J : ℂ) (β : ℂ) h
    (partitionFunctionComplex_mem_slitPlane_of_leeYangSubdomain G hβ J himπ)

/-- **`freeEnergyComplex` is analytic on the entire Lee-Yang subdomain**
(not just at a point). Since analyticity is local and
`leeYangSubdomain` is open, membership at each point lifts to
`AnalyticOnNhd` on the whole set. -/
theorem freeEnergyComplex_analyticOnNhd_leeYangSubdomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    AnalyticOnNhd ℂ (fun h' => freeEnergyComplex G (J : ℂ) h' (β : ℂ))
        (leeYangSubdomain β (Fintype.card ι)) := by
  intro h hmem
  exact freeEnergyComplex_analyticAt_h_of_leeYangSubdomain
    G hβ J hmem.2


end IsingModel
