import IsingModel.AmbientLattice
import IsingModel.BetaDerivative
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

/-- The pseudo-mass profile: `g(t, r, α) = 2 · exp(-t·r) / (1 + (t·r)^α)`.
For `r > 0` and `α ≥ 1`, this is a continuous, strictly decreasing function
of `t ≥ 0` with `g(0) = 2` and `g(t) → 0` as `t → ∞`. -/
noncomputable def pseudoMassG (α : ℕ) (r t : ℝ) : ℝ :=
  2 * Real.exp (-t * r) / (1 + (t * r) ^ α)

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

/-- `pseudoMassG` is at most 2 for `t ≥ 0` and `r > 0`. -/
theorem pseudoMassG_le_two (α : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    pseudoMassG α r t ≤ 2 := by
  unfold pseudoMassG
  have hdenom_pos : (0 : ℝ) < 1 + (t * r) ^ α := by
    have h : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht hr.le) α
    linarith
  rw [div_le_iff₀ hdenom_pos]
  have hexp : Real.exp (-t * r) ≤ 1 := by
    rw [neg_mul]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht hr.le))
  have hdenom_ge : 1 ≤ 1 + (t * r) ^ α := by
    have h : 0 ≤ (t * r) ^ α := pow_nonneg (mul_nonneg ht hr.le) α
    linarith
  nlinarith [Real.exp_pos (-t * r)]

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
  · -- 2 * exp(-t*r) ≤ 2 * exp(-s*r): exp is monotone and -t*r < -s*r
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
  · -- 2 * exp(-t*r) → 0 as t → ∞
    have h_tr_atTop : Filter.Tendsto (fun t : ℝ => t * r) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.atTop_mul_const hr
    have h_exp_zero : Filter.Tendsto (fun t : ℝ => Real.exp (-(t * r))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp h_tr_atTop
    have h_eq : ∀ t : ℝ, 2 * Real.exp (-t * r) = 2 * Real.exp (-(t * r)) := fun t => by
      congr 1; rw [neg_mul]
    simp_rw [h_eq]
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

end IsingModel
