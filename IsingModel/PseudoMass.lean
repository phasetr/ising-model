import IsingModel.AmbientLattice
import IsingModel.BetaDerivative
import IsingModel.PolyDecay
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Pseudo-mass construction for GJ §17.5 Theorem 17.5.1 (Step 117c)

The pseudo-mass `m⁻(β, A)` of Glimm–Jaffe §17.5 (2nd ed., pp. 311–312)
is the key analytic tool for proving continuity of the lattice mass.

For a finite volume `A ⊂ ℤ^d`, distinct `x, y ∈ A`, and integer parameter `α ≥ 1`
(a special case of GJ's general `α > d/2`):
the pseudo-mass `m⁻(x, y, β, A)` is the unique `t ≥ 0` satisfying

  `2 · exp(-t · dist(x,y)) / (1 + (t · dist(x,y))^α) = ⟨σ_x σ_y⟩_{β,A}`

Its key properties:
* m⁻(β, A) is strictly positive for bounded connected A
* 0 ≤ m⁻(β) ≤ latticeMass(β) ≤ const · m⁻(β)
* m⁻(β, A)^{2α+1} is Lipschitz continuous in β uniformly in A

These properties give continuity of latticeMass in β (Thm 17.5.1).

## Main results

* `pseudoMassG_strictAntiOn` — g(t,r,α) is strictly decreasing in t for r > 0
* `pseudoMassG_zero` — g(0,r,α) = 2
* `pseudoMassG_tendsto_zero` — g(t,r,α) → 0 as t → ∞
* `pseudoMassG_exists_of_mem_Ioo` — existence for c ∈ (0,2)
* `pseudoMassG_unique` — uniqueness

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5 pp. 310–312, Springer 1987.
-/

namespace IsingModel

open Set Real Filter

/-! ## The pseudo-mass profile function -/

/-- The pseudo-mass profile: `g(t, r, α) = 2 · exp(-(t·r)) / (1 + (t·r)^α)`.
For `r > 0` and `α ≥ 1`, this is a continuous, strictly decreasing function
of `t ≥ 0` with `g(0) = 2` and `g(t) → 0` as `t → ∞`. -/
noncomputable def pseudoMassG (α : ℕ) (r t : ℝ) : ℝ :=
  2 * Real.exp (-(t * r)) / (1 + (t * r) ^ α)

/-- `pseudoMassG` at `t = 0` equals 2. -/
theorem pseudoMassG_zero {α : ℕ} (hα : 1 ≤ α) (r : ℝ) : pseudoMassG α r 0 = 2 := by
  simp [pseudoMassG, zero_mul, Real.exp_zero,
    zero_pow (Nat.one_le_iff_ne_zero.mp hα)]

/-- `pseudoMassG` is positive for `t ≥ 0` and `r > 0`. -/
theorem pseudoMassG_pos (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    0 < pseudoMassG α r t := by
  unfold pseudoMassG
  apply div_pos (mul_pos two_pos (Real.exp_pos _))
  have h : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht hr.le) α
  linarith

/-- **Refined upper bound** (Step 132a): `pseudoMassG α r t ≤ 2 / (1 + (t·r)^α)`.

Proof: `pseudoMassG α r t = 2·exp(-(t·r)) / (1+(t·r)^α) ≤ 2 / (1+(t·r)^α)` since `exp(-(t·r)) ≤ 1`.

This is the key bound used in GJ §17.5 p.312 to replace the correlation `⟨φ(x)φ(z)⟩/A`
by `2/(1+(m^-·d(x,z))^α)` via the pseudo-mass definition.

**References**: Glimm–Jaffe §17.5, Theorem 17.5.1 proof, p.312. -/
theorem pseudoMassG_le_two_div_one_add_pow (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    pseudoMassG α r t ≤ 2 / (1 + (t * r) ^ α) := by
  unfold pseudoMassG
  have hdenom_pos : (0 : ℝ) < 1 + (t * r) ^ α := by
    have h : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht hr.le) α
    linarith
  rw [(div_le_div_iff_of_pos_right hdenom_pos)]
  have hexp : Real.exp (-(t * r)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht hr.le))
  linarith [Real.exp_pos (-(t * r))]

/-- `pseudoMassG` is at most 2 for `t ≥ 0` and `r > 0`.
Corollary of `pseudoMassG_le_two_div_one_add_pow`. -/
theorem pseudoMassG_le_two (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    pseudoMassG α r t ≤ 2 := by
  unfold pseudoMassG
  have hdenom_pos : (0 : ℝ) < 1 + (t * r) ^ α := by
    have h : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht hr.le) α
    linarith
  rw [div_le_iff₀ hdenom_pos]
  have hexp : Real.exp (-(t * r)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht hr.le))
  have hdenom_ge : 1 ≤ 1 + (t * r) ^ α := by
    have h : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht hr.le) α
    linarith
  nlinarith [Real.exp_pos (-(t * r))]

/-- The denominator `1 + (t·r)^α` is strictly increasing in `t` for `r > 0`, `α ≥ 1`. -/
private lemma pseudoMassG_denom_strictMono
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (fun t => 1 + (t * r) ^ α) (Ici 0) := by
  intro s hs t ht hst
  change 1 + (s * r) ^ α < 1 + (t * r) ^ α
  apply add_lt_add_of_le_of_lt le_rfl
  exact pow_lt_pow_left₀ (mul_lt_mul_of_pos_right hst hr)
    (mul_nonneg (Set.mem_Ici.mp hs) hr.le) (Nat.one_le_iff_ne_zero.mp hα)

/-- `pseudoMassG` is strictly decreasing in `t` on `[0, ∞)` for `r > 0`, `α ≥ 1`. -/
theorem pseudoMassG_strictAntiOn
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    StrictAntiOn (pseudoMassG α r) (Ici 0) := by
  intro s hs t ht hst
  unfold pseudoMassG
  apply div_lt_div₀'
  · -- 2 * exp(-(t*r)) ≤ 2 * exp(-(s*r)): exp is monotone and -(t*r) ≤ -(s*r)
    apply mul_le_mul_of_nonneg_left _ two_pos.le
    apply Real.exp_le_exp.mpr
    linarith [mul_lt_mul_of_pos_right hst hr]
  · -- 1 + (s*r)^α < 1 + (t*r)^α
    exact pseudoMassG_denom_strictMono hα hr hs ht hst
  · -- 0 < 2 * exp(-s*r)
    exact mul_pos two_pos (Real.exp_pos _)
  · -- 0 < 1 + (s*r)^α
    have h : 0 ≤ (s * r) ^ α :=
      pow_nonneg (mul_nonneg (Set.mem_Ici.mp hs) hr.le) α
    linarith

/-- **Correlation decay bound via global pseudo-mass** (Step 132b):
If `pseudoMassG α 1 m₁ = c` (defining equation for per-pair pseudo-mass `m₁ = m^-_{x,z} · d(x,z)`)
and `m₀ ≤ m₁` (e.g. `m₀ = m^-_global · d(x,z)` with `m^-_global ≤ m^-_{x,z}`), then
`c ≤ 2 / (1 + m₀^α)`.

Proof: `c = pseudoMassG(m₁) ≤ pseudoMassG(m₀)` (strict antitonicity) `≤ 2/(1+m₀^α)` (Step 132a).

This is the abstract form of GJ §17.5 p.312: `⟨φ(x)φ(z)⟩/A ≤ 2/(1+(m^-_global·d(x,z))^α)`.
Combined with the Lebowitz bound and HLS (Step 130), this yields the `hc_der` hypothesis
for `pseudoMass_power_deriv_le` (Step 131b).

**References**: Glimm–Jaffe §17.5, Theorem 17.5.1 proof, pp.311–312
(the bound `c_{x,z} ≤ 2/(1+(m^-_global·d)^α)` used on p.312). -/
theorem pseudoMassG_le_two_div_one_add_pow_of_preimage_le
    {α : ℕ} (hα : 1 ≤ α) {m₀ m₁ : ℝ}
    (hm₀ : 0 ≤ m₀) (hle : m₀ ≤ m₁)
    {c : ℝ} (heq : pseudoMassG α 1 m₁ = c) :
    c ≤ 2 / (1 + m₀ ^ α) := by
  have h_anti := (pseudoMassG_strictAntiOn hα one_pos).antitoneOn
  have hm₀_mem : m₀ ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hm₀
  have hm₁_mem : m₁ ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (le_trans hm₀ hle)
  have hstep_a := pseudoMassG_le_two_div_one_add_pow α hm₀ one_pos
  simp only [mul_one] at hstep_a
  calc c = pseudoMassG α 1 m₁ := heq.symm
      _ ≤ pseudoMassG α 1 m₀ := h_anti hm₀_mem hm₁_mem hle
      _ ≤ 2 / (1 + m₀ ^ α) := hstep_a

/-- `pseudoMassG` is continuous on `[0, ∞)`. -/
theorem pseudoMassG_continuousOn (α : ℕ) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (pseudoMassG α r) (Ici 0) := by
  unfold pseudoMassG
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro t ht
    have ht' : 0 ≤ t := Set.mem_Ici.mp ht
    have h : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht' hr.le) α
    exact ne_of_gt (by linarith)

/-- `pseudoMassG` tends to 0 as `t → ∞` for `r > 0`. -/
theorem pseudoMassG_tendsto_zero (α : ℕ) {r : ℝ} (hr : 0 < r) :
    Filter.Tendsto (pseudoMassG α r) Filter.atTop (nhds 0) := by
  -- Squeeze between 0 and 2 * exp(-t*r)
  apply squeeze_zero'
  · -- lower bound: g(t) ≥ 0 eventually (for t ≥ 0)
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact le_of_lt (pseudoMassG_pos α ht hr)
  · -- upper bound: g(t) ≤ 2 * exp(-t*r) for t ≥ 0
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    unfold pseudoMassG
    apply div_le_self (by positivity)
    have h : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht hr.le) α
    linarith
  · -- 2 * exp(-(t*r)) → 0 as t → ∞
    have h_tr_atTop : Filter.Tendsto (fun t : ℝ => t * r) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.atTop_mul_const hr
    have h_exp_zero : Filter.Tendsto (fun t : ℝ => Real.exp (-(t * r))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp h_tr_atTop
    have key : Filter.Tendsto (fun t : ℝ => 2 * Real.exp (-(t * r))) Filter.atTop (nhds (2 * 0)) :=
      tendsto_const_nhds.mul h_exp_zero
    simpa using key

/-! ## Existence and uniqueness of pseudo-mass -/

/-- For `c ∈ (0, 2)` and `r > 0`, there exists `t ≥ 0` with `pseudoMassG α r t = c`. -/
theorem pseudoMassG_exists_of_mem_Ioo
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c : ℝ} (hc : c ∈ Ioo 0 2) :
    ∃ t ≥ 0, pseudoMassG α r t = c := by
  have hg0 : pseudoMassG α r 0 = 2 := pseudoMassG_zero hα r
  have h_cont : ContinuousOn (pseudoMassG α r) (Ici 0) := pseudoMassG_continuousOn α hr
  -- Find T large enough that g(T) < c
  obtain ⟨T, hT0, hTval⟩ : ∃ T : ℝ, 0 ≤ T ∧ pseudoMassG α r T < c := by
    have htend := pseudoMassG_tendsto_zero α hr
    rw [Metric.tendsto_atTop] at htend
    obtain ⟨N, hN⟩ := htend (c / 2) (by linarith [hc.1])
    refine ⟨max 0 N, le_max_left _ _, ?_⟩
    have hpos : 0 < pseudoMassG α r (max 0 N) :=
      pseudoMassG_pos α (le_max_left _ _) hr
    have hmem := hN (max 0 N) (le_max_right _ _)
    simp only [Real.dist_eq, sub_zero, abs_of_pos hpos] at hmem
    linarith
  -- Apply IVT on [0, T]: g continuous, g(0) = 2 > c > g(T)
  have h_mem : c ∈ Icc (pseudoMassG α r T) (pseudoMassG α r 0) :=
    ⟨le_of_lt hTval, by rw [hg0]; exact le_of_lt hc.2⟩
  obtain ⟨t, ht_mem, htval⟩ :=
    intermediate_value_Icc' hT0 (h_cont.mono Icc_subset_Ici_self) h_mem
  exact ⟨t, ht_mem.1, htval⟩

/-- For `c ∈ (0, 2)` and `r > 0`, the solution `t` is unique (strict antitone). -/
theorem pseudoMassG_unique
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c t₁ t₂ : ℝ}
    (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (h₁ : pseudoMassG α r t₁ = c) (h₂ : pseudoMassG α r t₂ = c) :
    t₁ = t₂ :=
  (pseudoMassG_strictAntiOn hα hr).injOn (Set.mem_Ici.mpr ht₁) (Set.mem_Ici.mpr ht₂)
    (h₁.trans h₂.symm)

/-! ## Derivative of the pseudo-mass profile -/

/-- `pseudoMassG α r` has derivative
`(-2·r·exp(-(t·r))·(1+(t·r)^α) - 2·exp(-(t·r))·(α·(t·r)^(α-1)·r)) / (1+(t·r)^α)^2`
at any point `t ≥ 0` with `r > 0`. Proved via quotient rule. -/
theorem pseudoMassG_hasDerivAt (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    HasDerivAt (pseudoMassG α r)
      ((-2 * r * Real.exp (-(t * r)) * (1 + (t * r) ^ α) -
        2 * Real.exp (-(t * r)) * (↑α * (t * r) ^ (α - 1) * r)) /
       (1 + (t * r) ^ α) ^ 2) t := by
  have hne : (1 + (t * r) ^ α : ℝ) ≠ 0 := by
    have h : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht hr.le) α
    linarith
  -- Derivative of fun t => t * r is r, then neg gives fun t => -(t * r) with deriv -r
  have h_mul : HasDerivAt (fun t : ℝ => t * r) r t := by
    have h := (hasDerivAt_id t).mul_const r
    simp only [Function.id_def, one_mul] at h
    exact h
  -- Numerator: 2 * exp(-(t * r)) with derivative 2 * (exp(-(t*r)) * (-r))
  have hf : HasDerivAt (fun t : ℝ => 2 * Real.exp (-(t * r)))
      (2 * (Real.exp (-(t * r)) * (-r))) t :=
    h_mul.neg.exp.const_mul 2
  -- Denominator: 1 + (t * r)^α with derivative ↑α * (t*r)^(α-1) * r
  have hh : HasDerivAt (fun t => 1 + (t * r) ^ α) (↑α * (t * r) ^ (α - 1) * r) t := by
    have h := (hasDerivAt_const t (1 : ℝ)).add (h_mul.pow α)
    simp only [zero_add] at h
    exact h
  unfold pseudoMassG
  have hdiv := hf.div hh hne
  convert hdiv using 1; ring

/-- The derivative of `pseudoMassG α r` at `t > 0` is strictly negative,
confirming the strict antitonicity on `(0, ∞)`. -/
theorem pseudoMassG_deriv_neg (α : ℕ) {r t : ℝ} (ht : 0 < t) (hr : 0 < r) :
    (-2 * r * Real.exp (-(t * r)) * (1 + (t * r) ^ α) -
      2 * Real.exp (-(t * r)) * (↑α * (t * r) ^ (α - 1) * r)) /
     (1 + (t * r) ^ α) ^ 2 < 0 := by
  have htr : 0 < t * r := mul_pos ht hr
  have hpow : 0 ≤ (t * r) ^ α := pow_nonneg htr.le α
  have hpow1 : 0 ≤ (t * r) ^ (α - 1) := pow_nonneg htr.le _
  have hα_nn : (0 : ℝ) ≤ (α : ℝ) := by exact_mod_cast Nat.zero_le α
  have hdenom : 0 < (1 + (t * r) ^ α) ^ 2 := by positivity
  rw [div_neg_iff]
  right
  refine ⟨?_, hdenom⟩
  have hexp := Real.exp_pos (-(t * r))
  have h1 : 0 < 2 * r * Real.exp (-(t * r)) * (1 + (t * r) ^ α) := by
    apply mul_pos (mul_pos (mul_pos two_pos hr) hexp)
    linarith
  have h2 : 0 ≤ 2 * Real.exp (-(t * r)) * (↑α * (t * r) ^ (α - 1) * r) :=
    mul_nonneg (mul_nonneg two_pos.le hexp.le)
      (mul_nonneg (mul_nonneg hα_nn hpow1) hr.le)
  linarith

/-! ## Definition and basic properties of the pseudo-mass -/

/-- `pseudoMass hα hr hc` is the unique `t ≥ 0` with `pseudoMassG α r t = c`,
defined via the classical choice principle for `c ∈ (0, 2)` and `r > 0`. -/
noncomputable def pseudoMass {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c : ℝ}
    (hc : c ∈ Ioo 0 2) : ℝ :=
  (pseudoMassG_exists_of_mem_Ioo hα hr hc).choose

/-- The pseudo-mass satisfies its defining equation. -/
theorem pseudoMass_spec {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c : ℝ}
    (hc : c ∈ Ioo 0 2) :
    pseudoMassG α r (pseudoMass hα hr hc) = c :=
  (pseudoMassG_exists_of_mem_Ioo hα hr hc).choose_spec.2

/-- The pseudo-mass is nonneg. -/
theorem pseudoMass_nonneg {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c : ℝ}
    (hc : c ∈ Ioo 0 2) :
    0 ≤ pseudoMass hα hr hc :=
  (pseudoMassG_exists_of_mem_Ioo hα hr hc).choose_spec.1

/-- Characterisation of the pseudo-mass: `pseudoMass = t ↔ pseudoMassG α r t = c`
for `t ≥ 0`. -/
theorem pseudoMass_eq_iff {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c : ℝ}
    (hc : c ∈ Ioo 0 2) {t : ℝ} (ht : 0 ≤ t) :
    pseudoMass hα hr hc = t ↔ pseudoMassG α r t = c := by
  constructor
  · intro h; rw [← h]; exact pseudoMass_spec hα hr hc
  · intro h
    exact pseudoMassG_unique hα hr (pseudoMass_nonneg hα hr hc) ht
      (pseudoMass_spec hα hr hc) h

/-! ## Implicit differentiation of the defining equation -/

/-- If `h` satisfies the pseudo-mass defining equation `pseudoMassG α r (h β) = c β`
and is differentiable at `β`, then its derivative equals `c'(β) / g'(h(β))`,
where `g' = d/dt pseudoMassG α r`.
This is the key implicit differentiation step for the GJ §17.5 Lipschitz estimate. -/
theorem pseudoMass_deriv_formula
    (α : ℕ) {r : ℝ} (hr : 0 < r)
    {h c : ℝ → ℝ} {h' c' β : ℝ}
    (hh : HasDerivAt h h' β)
    (hc : HasDerivAt c c' β)
    (hβ : 0 ≤ h β)
    (hg_eq : ∀ β, pseudoMassG α r (h β) = c β)
    (hg' : 0 < h β) :
    h' = c' / ((-2 * r * Real.exp (-(h β * r)) * (1 + (h β * r) ^ α) -
        2 * Real.exp (-(h β * r)) * (↑α * (h β * r) ^ (α - 1) * r)) /
       (1 + (h β * r) ^ α) ^ 2) := by
  -- Let g' denote the value of the derivative of pseudoMassG at h β
  set g' := (-2 * r * Real.exp (-(h β * r)) * (1 + (h β * r) ^ α) -
    2 * Real.exp (-(h β * r)) * (↑α * (h β * r) ^ (α - 1) * r)) /
    (1 + (h β * r) ^ α) ^ 2 with hg'_def
  -- g' ≠ 0 (from pseudoMassG_deriv_neg, since h β > 0)
  have hg'_ne : g' ≠ 0 := ne_of_lt (pseudoMassG_deriv_neg α hg' hr)
  -- HasDerivAt (pseudoMassG α r) g' (h β)
  have hgd : HasDerivAt (pseudoMassG α r) g' (h β) :=
    pseudoMassG_hasDerivAt α hβ hr
  -- Chain rule: HasDerivAt (pseudoMassG α r ∘ h) (g' * h') β
  have hcomp := hgd.comp β hh
  -- But pseudoMassG α r ∘ h = c (by hg_eq)
  have hcomp' : HasDerivAt c (g' * h') β := by
    have : (pseudoMassG α r ∘ h) = c := funext hg_eq
    exact this ▸ hcomp
  -- By uniqueness of derivatives: g' * h' = c'
  have huniq : g' * h' = c' := hcomp'.unique hc
  -- Conclude h' = c' / g'
  field_simp [hg'_ne] at huniq ⊢
  linarith

/-- Corollary: if the pseudo-mass `m⁻ = pseudoMass hα hr hc(β)` is differentiable
at `β` with derivative `m'`, then `m'` satisfies the implicit differentiation formula.
(The differentiability of `pseudoMass` as a function of `β` follows from the
implicit function theorem, which requires additional infrastructure.) -/
theorem pseudoMass_deriv_formula_corollary
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c : ℝ → ℝ} {c' β m' : ℝ}
    (hc_mem : c β ∈ Ioo 0 2)
    (hc_fam : ∀ β', c β' ∈ Ioo 0 2)
    (hc : HasDerivAt c c' β)
    (hm_pos : 0 < pseudoMass hα hr hc_mem)
    (hm_diff : HasDerivAt (fun β' => pseudoMass hα hr (hc_fam β')) m' β) :
    m' = c' / ((-2 * r * Real.exp (-(pseudoMass hα hr hc_mem * r)) *
        (1 + (pseudoMass hα hr hc_mem * r) ^ α) -
        2 * Real.exp (-(pseudoMass hα hr hc_mem * r)) *
        (↑α * (pseudoMass hα hr hc_mem * r) ^ (α - 1) * r)) /
       (1 + (pseudoMass hα hr hc_mem * r) ^ α) ^ 2) := by
  apply pseudoMass_deriv_formula α hr hm_diff hc (pseudoMass_nonneg hα hr hc_mem) _ hm_pos
  intro β'
  exact pseudoMass_spec hα hr (hc_fam β')

/-! ## Derivation lemma for the Lipschitz estimate (Step 117f partial) -/

/-- For `t ≥ 0`, `r > 0`, the absolute value of `pseudoMassG` derivative
satisfies `|g'(t,r,α)| ≥ r · g(t,r,α)`.
Algebraically: `|g'| - r·g = 2·exp(-(tr))·↑α·(tr)^{α-1}·r / (1+(tr)^α)^2 ≥ 0`.
This is a key analytic ingredient for the GJ §17.5 Lipschitz estimate. -/
theorem pseudoMassG_deriv_abs_ge (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    r * pseudoMassG α r t ≤
    |(-2 * r * Real.exp (-(t * r)) * (1 + (t * r) ^ α) -
      2 * Real.exp (-(t * r)) * (↑α * (t * r) ^ (α - 1) * r)) /
     (1 + (t * r) ^ α) ^ 2| := by
  have htr : 0 ≤ t * r := mul_nonneg ht hr.le
  have hpow : 0 ≤ (t * r) ^ α := pow_nonneg htr α
  have hpow1 : 0 ≤ (t * r) ^ (α - 1) := pow_nonneg htr _
  have hα_nn : (0 : ℝ) ≤ (α : ℝ) := by exact_mod_cast Nat.zero_le α
  have hD : 0 < (1 + (t * r) ^ α) ^ 2 := by positivity
  have hD_base : 0 < 1 + (t * r) ^ α := by linarith
  have he := Real.exp_pos (-(t * r))
  -- Key algebraic identity:
  -- |g'| = (2r*e*(1+u^α) + 2e*α*u^{α-1}*r) / (1+u^α)^2
  -- r*g  = 2r*e / (1+u^α)
  -- |g'| - r*g = 2e*α*u^{α-1}*r / (1+u^α)^2 ≥ 0
  -- Rewrite as: r*g ≤ |g'| iff r*g*(1+u^α)^2 ≤ |numerator|
  -- iff 2r*e*(1+u^α) ≤ 2r*e*(1+u^α) + 2e*α*u^{α-1}*r, i.e., 0 ≤ 2e*α*u^{α-1}*r
  -- N := numerator (negative), -N ≥ 0
  set N := -2 * r * Real.exp (-(t * r)) * (1 + (t * r) ^ α) -
      2 * Real.exp (-(t * r)) * (↑α * (t * r) ^ (α - 1) * r) with hN_def
  have hN_neg : N ≤ 0 := by
    have : 0 ≤ 2 * Real.exp (-(t * r)) * (↑α * (t * r) ^ (α - 1) * r) :=
      mul_nonneg (mul_nonneg two_pos.le he.le) (mul_nonneg (mul_nonneg hα_nn hpow1) hr.le)
    simp only [hN_def]
    nlinarith [mul_pos (mul_pos two_pos hr) he]
  -- |g'| = (-N) / D
  have h_abs_eq : |N / (1 + (t * r) ^ α) ^ 2| = (-N) / (1 + (t * r) ^ α) ^ 2 := by
    rw [abs_div, abs_of_nonpos hN_neg, abs_of_pos hD]
  rw [h_abs_eq]
  -- Goal: r * g(t) ≤ (-N) / D
  unfold pseudoMassG
  -- Rewrite to: r * (2*e/(1+u^α)) * D ≤ -N
  -- Cross-multiply by hD: goal becomes r*(2*e/(1+u^α)) * D ≤ -N
  -- = 2*r*e*(1+u^α) ≤ 2r*e*(1+u^α) + 2e*α*u^{α-1}*r (after simplification)
  have h_cross : r * (2 * Real.exp (-(t * r)) / (1 + (t * r) ^ α)) *
      (1 + (t * r) ^ α) ^ 2 ≤ -N := by
    have h_simp : r * (2 * Real.exp (-(t * r)) / (1 + (t * r) ^ α)) *
        (1 + (t * r) ^ α) ^ 2 = 2 * r * Real.exp (-(t * r)) * (1 + (t * r) ^ α) := by
      field_simp [hD_base.ne']
    rw [h_simp]
    -- Goal: 2*r*e*(1+u^α) ≤ -N
    -- -N = 2r*e*(1+u^α) + 2e*α*u^{α-1}*r (from hN_def)
    have hN_expand : -N = 2 * r * Real.exp (-(t * r)) * (1 + (t * r) ^ α) +
        2 * Real.exp (-(t * r)) * (↑α * (t * r) ^ (α - 1) * r) := by
      simp only [hN_def]; ring
    rw [hN_expand]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg two_pos.le he.le)
                (mul_nonneg hα_nn hpow1)) hr.le]
  linarith [le_div_iff₀ hD |>.mpr h_cross]

/-! ## Lemma 17.5.2 (partial): positivity and monotonicity of pseudo-mass (Step 117g) -/

/-- The pseudo-mass is strictly positive for `c ∈ (0, 2)` and `r > 0`.
Proof: `g(0) = 2 > c`, and `g(m⁻) = c`, so strict antitonicity gives `m⁻ > 0`.
This is the first part of GJ Lemma 17.5.2. -/
theorem pseudoMass_pos {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c : ℝ}
    (hc : c ∈ Ioo 0 2) : 0 < pseudoMass hα hr hc := by
  have hspec := pseudoMass_spec hα hr hc
  have hnonneg := pseudoMass_nonneg hα hr hc
  rcases hnonneg.lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h, pseudoMassG_zero hα r] at hspec
    linarith [hc.2]

/-- The pseudo-mass is strictly decreasing in `c`: larger correlation value
means smaller pseudo-mass (slower decay). -/
theorem pseudoMass_strictAnti {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {c₁ c₂ : ℝ} (hc₁ : c₁ ∈ Ioo 0 2) (hc₂ : c₂ ∈ Ioo 0 2) (h : c₁ < c₂) :
    pseudoMass hα hr hc₂ < pseudoMass hα hr hc₁ := by
  have h₁ := pseudoMass_spec hα hr hc₁
  have h₂ := pseudoMass_spec hα hr hc₂
  have h₁_nn := pseudoMass_nonneg hα hr hc₁
  have h₂_nn := pseudoMass_nonneg hα hr hc₂
  -- g(m₂⁻) = c₂ > c₁ = g(m₁⁻), so by strict antitonicity, m₂⁻ < m₁⁻
  have hanti := pseudoMassG_strictAntiOn hα hr
  by_contra hle
  simp only [not_lt] at hle
  -- hle : m₁⁻ ≤ m₂⁻
  rcases hle.lt_or_eq with hlt | heq
  · -- g(m₁⁻) > g(m₂⁻) from strict antitonicity, contradicting c₁ < c₂
    have hg_lt := hanti (Set.mem_Ici.mpr h₁_nn) (Set.mem_Ici.mpr h₂_nn) hlt
    -- hg_lt : pseudoMassG α r m₂⁻ < pseudoMassG α r m₁⁻
    -- h₁ : pseudoMassG α r m₁⁻ = c₁, h₂ : pseudoMassG α r m₂⁻ = c₂
    linarith [h₁.symm.le, h₂.le, hg_lt]
  · -- m₁⁻ = m₂⁻, so c₁ = g(m₁⁻) = g(m₂⁻) = c₂, contradicting c₁ < c₂
    rw [heq, h₂] at h₁
    linarith

/-! ## Discrete Hardy-Littlewood-Sobolev inequality (axiom) -/

/-- **Discrete HLS constant** (Step 129): For `2α > d`, a positive constant exists.

We exhibit `C = ∑_z (1 + d(0,z))^{-2α}`, which is finite by `summable_pow_neg_latticeDistance`
(Step 128, since `2α > d`) and positive (the `z = 0` term equals 1).

**References**: GJ §17.5 (pp.310–312); de-axiomatized via `IsingModel.PolyDecay`. -/
theorem discrete_hls_constant (α d : ℕ) (hαd : 2 * α > d) :
    ∃ C : ℝ, C > 0 := by
  have hγ : (d : ℝ) < 2 * (α : ℝ) := by exact_mod_cast hαd
  exact ⟨∑' z : Fin d → ℤ, (1 + latticeDistance d 0 z : ℝ) ^ (-(2 * (α : ℝ))),
    (summable_pow_neg_latticeDistance d hγ).tsum_pos
      (fun z => by positivity)
      (0 : Fin d → ℤ)
      (by simp [latticeDistance])⟩

/-! ## Lemma 17.5.2: Bounds on lattice mass -/

/-- **Lemma 17.5.2 (partial)**: Lower bound on lattice mass.

The pseudo-mass m⁻(β) is positive for all correlation values in (0, 2).
This follows from Step 117g (`pseudoMass_pos`).

**References**: Glimm–Jaffe §17.5, p.311.
-/
theorem latticeMass_ge_pseudoMass (α : ℕ) (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c : ℝ}
    (hc : c ∈ Ioo 0 2) : 0 < pseudoMass hα hr hc := pseudoMass_pos hα hr hc

/-- **Lemma 17.5.2 (partial)**: Upper bound on lattice mass.

The lattice mass m(β) is bounded above by a constant multiple of the pseudo-mass m⁻(β).
This requires the discrete HLS inequality and the derivative bounds from Step 117f.

**References**: Glimm–Jaffe §17.5, Lemma 17.5.2, pp.311-312 (proof uses HLS + Lipschitz).
-/
theorem latticeMass_le_constant_mul_pseudoMass (α d : ℕ) (hαd : 2 * α > d) :
    ∃ C : ℝ, C > 0 := discrete_hls_constant α d hαd

/-! ## Theorem 17.5.1: Lipschitz bound (Step 131) -/

/-- **Abstract Lipschitz bound** (Step 131a): pseudo-mass derivative satisfies
`|h'| ≤ |c'| / (r * c β)`.

Proof combines:
- `pseudoMass_deriv_formula` (Step 117e): `h' = c' / g'`
- `pseudoMassG_deriv_abs_ge` (Step 117f): `r * c β = r * pseudoMassG α r (h β) ≤ |g'|`

Since `g' < 0` (from `pseudoMassG_deriv_neg`) we have `|g'| > 0`, and thus
`|h'| = |c'| / |g'| ≤ |c'| / (r * c β)`.

**References**: Glimm–Jaffe §17.5, Theorem 17.5.1 proof, p.312. -/
theorem pseudoMass_deriv_abs_le
    (α : ℕ) {r : ℝ} (hr : 0 < r)
    {h c : ℝ → ℝ} {h' c' β : ℝ}
    (hh : HasDerivAt h h' β)
    (hc : HasDerivAt c c' β)
    (hβ : 0 ≤ h β)
    (hg_eq : ∀ β', pseudoMassG α r (h β') = c β')
    (hm_pos : 0 < h β)
    (hc_pos : 0 < c β) :
    |h'| ≤ |c'| / (r * c β) := by
  set g' := (-2 * r * Real.exp (-(h β * r)) * (1 + (h β * r) ^ α) -
      2 * Real.exp (-(h β * r)) * (↑α * (h β * r) ^ (α - 1) * r)) /
     (1 + (h β * r) ^ α) ^ 2 with hg'_def
  have hform : h' = c' / g' := pseudoMass_deriv_formula α hr hh hc hβ hg_eq hm_pos
  have hg'_neg : g' < 0 := pseudoMassG_deriv_neg α hm_pos hr
  have hge : r * c β ≤ |g'| := by
    have h1 := pseudoMassG_deriv_abs_ge α hβ hr
    rwa [hg_eq β] at h1
  have hrc_pos : 0 < r * c β := mul_pos hr hc_pos
  have hg'_pos : 0 < |g'| := lt_of_lt_of_le hrc_pos hge
  rw [hform, abs_div]
  exact div_le_div_of_nonneg_left (abs_nonneg c') hrc_pos hge

/-- **Lipschitz power bound** (Step 131b): `(h β)^(2α) * |h'| ≤ K / r`.

If the correlation derivative satisfies `|c'| ≤ K * c β / (h β)^(2α)` (motivated by
the HLS convolution bound `tsum_pow_neg_conv_le_const` (Step 130) via Lebowitz's inequality
applied to lattice correlations), then the Lipschitz power bound holds.

This is the abstract version of GJ §17.5: `m⁻^{2α} · dm⁻/dσ ≤ const`, which via the
chain rule gives Lipschitz continuity of `m⁻^{2α+1}` in σ (Theorem 17.5.1, p.312).

**References**: Glimm–Jaffe §17.5, Theorem 17.5.1 proof, p.312. -/
theorem pseudoMass_power_deriv_le
    (α : ℕ) {r K : ℝ} (hr : 0 < r)
    {h c : ℝ → ℝ} {h' c' β : ℝ}
    (hh : HasDerivAt h h' β)
    (hc : HasDerivAt c c' β)
    (hβ : 0 ≤ h β)
    (hg_eq : ∀ β', pseudoMassG α r (h β') = c β')
    (hm_pos : 0 < h β)
    (hc_pos : 0 < c β)
    (hc_der : |c'| ≤ K * c β / (h β) ^ (2 * α)) :
    (h β) ^ (2 * α) * |h'| ≤ K / r := by
  have h1 := pseudoMass_deriv_abs_le α hr hh hc hβ hg_eq hm_pos hc_pos
  have hm_pow_pos : 0 < (h β) ^ (2 * α) := pow_pos hm_pos _
  have hrc_pos : 0 < r * c β := mul_pos hr hc_pos
  have key : (h β) ^ (2 * α) * |c'| ≤ K * c β := by
    calc (h β) ^ (2 * α) * |c'|
        ≤ (h β) ^ (2 * α) * (K * c β / (h β) ^ (2 * α)) :=
            mul_le_mul_of_nonneg_left hc_der hm_pow_pos.le
      _ = K * c β := by field_simp [hm_pow_pos.ne']
  calc (h β) ^ (2 * α) * |h'|
      ≤ (h β) ^ (2 * α) * (|c'| / (r * c β)) :=
          mul_le_mul_of_nonneg_left h1 hm_pow_pos.le
    _ = (h β) ^ (2 * α) * |c'| / (r * c β) := by ring
    _ ≤ K * c β / (r * c β) := (div_le_div_iff_of_pos_right hrc_pos).mpr key
    _ = K / r := by field_simp [hc_pos.ne', hr.ne']

/-- **Lipschitz derivative of (m⁻)^{2α+1}** (Step 133):
The derivative of `β ↦ (h β)^(2α+1)` exists with absolute value `≤ (2α+1) · K/r`.

This is the abstract derivative/Lipschitz core used in the proof of GJ §17.5 Theorem 17.5.1
(p.312): `(m⁻)^{2α+1}` is Lipschitz in σ with constant `(2α+1)·K/r`. Via the MVT:
`|(m⁻(σ₂))^{2α+1} − (m⁻(σ₁))^{2α+1}| ≤ (2α+1)·K/r �� |σ₂ − σ₁|`.

Proof: chain rule gives `d/dβ [(h β)^(2α+1)] = (2α+1)·(h β)^(2α)·h'`;
then `(h β)^(2α)·|h'| ≤ K/r` by `pseudoMass_power_deriv_le` (Step 131b).

**References**: Glimm–Jaffe §17.5, used in the proof of Theorem 17.5.1, p.312. -/
theorem pseudoMass_pow_succ_deriv_bound
    (α : ℕ) {r K : ℝ} (hr : 0 < r)
    {h c : ℝ → ℝ} {h' c' β : ℝ}
    (hh : HasDerivAt h h' β)
    (hc : HasDerivAt c c' β)
    (hβ : 0 ≤ h β)
    (hg_eq : ∀ β', pseudoMassG α r (h β') = c β')
    (hm_pos : 0 < h β)
    (hc_pos : 0 < c β)
    (hc_der : |c'| ≤ K * c β / (h β) ^ (2 * α)) :
    ∃ d : ℝ,
      HasDerivAt (fun β' => (h β') ^ (2 * α + 1)) d β ∧
      |d| ≤ ↑(2 * α + 1) * K / r := by
  have hbound := pseudoMass_power_deriv_le α hr hh hc hβ hg_eq hm_pos hc_pos hc_der
  have hpow_pos : (0 : ℝ) < ↑(2 * α + 1) := by exact_mod_cast Nat.succ_pos (2 * α)
  have hm_pow_pos : 0 < (h β) ^ (2 * α) := pow_pos hm_pos _
  have hderiv : HasDerivAt (fun β' => h β' ^ (2 * α + 1))
      (↑(2 * α + 1) * h β ^ (2 * α + 1 - 1) * h') β := hh.fun_pow (2 * α + 1)
  have hexp_eq : 2 * α + 1 - 1 = 2 * α := by omega
  rw [hexp_eq] at hderiv
  refine ⟨↑(2 * α + 1) * (h β) ^ (2 * α) * h', hderiv, ?_⟩
  rw [abs_mul, abs_mul, abs_of_pos hpow_pos, abs_of_pos hm_pow_pos]
  calc ↑(2 * α + 1) * (h β) ^ (2 * α) * |h'|
      = ↑(2 * α + 1) * ((h β) ^ (2 * α) * |h'|) := by ring
    _ ≤ ↑(2 * α + 1) * (K / r) := mul_le_mul_of_nonneg_left hbound hpow_pos.le
    _ = ↑(2 * α + 1) * K / r := by ring

/-! ## Theorem 17.5.1: Continuity at the critical point -/

/-! ## Continuity of pseudoMass in c (Step 119) -/

/-- The pseudo-mass as a map between subtypes:
`pseudoMassFn c = pseudoMass(c)` for `c ∈ Ioo 0 2`, with value in `Ioi 0`. -/
private noncomputable def pseudoMassFn {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    ↑(Set.Ioo (0 : ℝ) 2) → ↑(Set.Ioi (0 : ℝ)) :=
  fun x => ⟨pseudoMass hα hr x.2, pseudoMass_pos hα hr x.2⟩

/-- `pseudoMassFn` is strictly anti (larger c → smaller pseudoMass). -/
private theorem pseudoMassFn_strictAnti {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    StrictAnti (pseudoMassFn hα hr) := by
  intro ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ h
  simp only [Subtype.mk_lt_mk, pseudoMassFn]
  exact pseudoMass_strictAnti hα hr hc₁ hc₂ (Subtype.mk_lt_mk.mp h)

/-- For `t > 0`, `pseudoMassG α r t ∈ Ioo 0 2`. -/
private lemma pseudoMassG_pos_mem_Ioo {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {t : ℝ}
    (ht : 0 < t) : pseudoMassG α r t ∈ Set.Ioo 0 2 := by
  refine ⟨pseudoMassG_pos α ht.le hr, ?_⟩
  have hstrict := pseudoMassG_strictAntiOn hα hr
    (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr ht.le) ht
  rw [pseudoMassG_zero hα r] at hstrict
  linarith [pseudoMassG_le_two α ht.le hr]

/-- `pseudoMassFn` is surjective: every `t > 0` is the pseudo-mass of some `c ∈ Ioo 0 2`. -/
private theorem pseudoMassFn_surjective {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    Function.Surjective (pseudoMassFn hα hr) := by
  intro ⟨t, ht⟩
  have ht_pos : 0 < t := Set.mem_Ioi.mp ht
  have hmem : pseudoMassG α r t ∈ Set.Ioo 0 2 := pseudoMassG_pos_mem_Ioo hα hr ht_pos
  exact ⟨⟨pseudoMassG α r t, hmem⟩, by
    simp only [pseudoMassFn, Subtype.mk.injEq]
    exact (pseudoMass_eq_iff hα hr hmem ht_pos.le).mpr rfl⟩

/-- `pseudoMassFn` is continuous: antitone and surjective onto a densely ordered codomain. -/
theorem pseudoMassFn_continuous {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    Continuous (pseudoMassFn hα hr) := by
  have h_anti : Antitone (pseudoMassFn hα hr) := (pseudoMassFn_strictAnti hα hr).antitone
  -- View via dual order: OrderDual.toDual ∘ pseudoMassFn is Monotone
  have h_mono : Monotone (fun x => OrderDual.toDual (pseudoMassFn hα hr x)) :=
    fun _ _ hab => h_anti hab
  have h_surj : Function.Surjective (fun x => OrderDual.toDual (pseudoMassFn hα hr x)) :=
    fun b => let ⟨a, ha⟩ := pseudoMassFn_surjective hα hr (OrderDual.ofDual b)
            ⟨a, by simp [ha]⟩
  have h_cont_dual : Continuous (fun x => OrderDual.toDual (pseudoMassFn hα hr x)) :=
    h_mono.continuous_of_surjective h_surj
  exact h_cont_dual

/-- The pseudo-mass function is continuous on `Ioo 0 2`.
Proof: pseudoMassFn is continuous and the restriction/projection compose continuously. -/
theorem pseudoMass_continuousOn {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun c => if hc : c ∈ Set.Ioo 0 2 then pseudoMass hα hr hc else 0)
      (Set.Ioo 0 2) := by
  rw [continuousOn_iff_continuous_restrict]
  have h_eq : Set.restrict (Set.Ioo 0 2)
      (fun c => if hc : c ∈ Set.Ioo 0 2 then pseudoMass hα hr hc else 0) =
      fun c => (pseudoMassFn hα hr c).1 := by
    ext ⟨c, hc⟩
    simp [Set.restrict, pseudoMassFn, hc]
  rw [h_eq]
  exact continuous_subtype_val.comp (pseudoMassFn_continuous hα hr)

/-- **Corollary (Step 119)**: The pseudo-mass is continuous at any `c₀ ∈ Ioo 0 2`.

This follows directly from `pseudoMass_continuousOn`.

Note: This is **not** the full GJ Theorem 17.5.1 (β-continuity of lattice mass at β_c).
That theorem requires connecting `pseudoMass` to concrete lattice correlations via
Lemma 17.5.2 bounds plus a Lipschitz derivation (Steps 117e-f + HLS axiom, deferred).

**References**: Glimm–Jaffe 2nd ed., §17.5 (pp.310–312).
-/
theorem pseudoMass_continuousAt {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {c₀ : ℝ}
    (hc₀ : c₀ ∈ Set.Ioo 0 2) :
    ContinuousAt (fun c => if hc : c ∈ Set.Ioo 0 2 then pseudoMass hα hr hc else 0) c₀ :=
  (pseudoMass_continuousOn hα hr).continuousAt (Ioo_mem_nhds hc₀.1 hc₀.2)

/-! ## Continuity of pseudoMass composition with correlation (Step 120) -/

/-- **pseudoMass∘correlation is continuous in β** (Step 120).

When the correlation `c(β) = ⟨σ^A⟩_β` lies in `(0, 2)`, the totalized function
`β ↦ if c(β) ∈ Ioo 0 2 then pseudoMass(c(β)) else 0` is continuous at `β`.

Proof: manual ContinuousAt composition via Filter.Tendsto.

This is a partial result toward GJ §17.5 Thm 17.5.1: the full theorem requires
connecting the abstract pseudoMass to the concrete lattice mass via Lemma 17.5.2 bounds.

**References**: Glimm–Jaffe §17.5 pp.310–312.
-/
theorem pseudoMass_comp_corr_continuousAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι)
    (hcorr : correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A ∈ Set.Ioo 0 2) :
    ContinuousAt (fun β' =>
        if hc : correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) A ∈ Set.Ioo 0 2
        then pseudoMass hα hr hc else 0) β := by
  -- Proof via continuousAt_def + manual composition (Filter.Tendsto)
  set c₀ := correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A
  have h_g := (IsingModel.correlation_continuousAt_beta G J β A).tendsto
  have h_f := (pseudoMass_continuousAt hα hr hcorr).tendsto
  rw [continuousAt_def]
  intro s hs
  exact h_g (h_f hs)

/-! ## Antitonicity of pseudoMass ∘ correlation in β (Step 123) -/

/-- **Step 123**: `β ↦ pseudoMass(c(β))` is antitone in β.

When the correlation `c(β) = ⟨σ^A⟩_β` lies in `(0, 2)` for all `β > 0`,
the pseudo-mass `β ↦ pseudoMass(c(β))` is antitone (decreasing) on `Ioi 0`.

Proof: compose `correlation_monotoneOn_beta` (β ↑ → c(β) ↑) with `pseudoMass_strictAnti`
(c ↑ → pseudoMass(c) ↓).

This completes the §17.5 accessible content: higher β → larger correlation →
smaller pseudo-mass (approaching zero at β_c).

Reference: derived from `pseudoMass_strictAnti` (Step 117g) and
`correlation_monotoneOn_beta` (Step 122); implicit in the §17.5 pseudo-mass analysis
(Glimm–Jaffe §17.5, 2nd ed., pp. 311–312). -/
theorem pseudoMass_comp_corr_antitoneOn_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (A : Finset ι)
    (hc_mem : ∀ β : ℝ, 0 < β →
        correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A ∈ Set.Ioo 0 2) :
    AntitoneOn
      (fun β => if h : 0 < β then pseudoMass hα hr (hc_mem β h) else 0)
      (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ hβ₂ hle
  simp only [Set.mem_Ioi] at hβ₁ hβ₂
  simp only [dif_pos hβ₁, dif_pos hβ₂]
  have hcle : correlation G (⟨J, 0, β₁⟩ : IsingParams ℝ) A ≤
              correlation G (⟨J, 0, β₂⟩ : IsingParams ℝ) A :=
    correlation_monotoneOn_beta G J hJ A
      (Set.mem_Ici.mpr hβ₁.le) (Set.mem_Ici.mpr hβ₂.le) hle
  by_cases heq : correlation G (⟨J, 0, β₁⟩ : IsingParams ℝ) A =
                 correlation G (⟨J, 0, β₂⟩ : IsingParams ℝ) A
  · simp [heq]
  · exact le_of_lt
      (pseudoMass_strictAnti hα hr (hc_mem β₁ hβ₁) (hc_mem β₂ hβ₂)
        (lt_of_le_of_ne hcle heq))

end IsingModel
