import IsingModel.Concrete.LatticeGraphCorrelation.SimonLiebDistanceDecay
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferSummability
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPointTruncatedInfiniteTrivialSlice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPointTruncatedInfiniteBounds

/-!
# Substantive HLS bundle: Simon-Lieb → HasExponentialDecay → tsum bound

GJ-proposition-unit bundle bridging Step 5.7h (PR #3179) Simon-Lieb
exp-form correlation bound with existing `tsum_truncated2Infinite_prod_le`
(`LatticeMassPseudoMassTransferSummability.lean`) via the `h = 0` identity
`truncated2Infinite_h_zero`.

This is the **substantive HLS sum bound** connection — for ferromagnetic
high-temperature at `h = 0`, the per-pair exponential correlation decay
from Simon-Lieb feeds into the existing infinite-sum bound machinery to
yield concrete tsum product bounds with explicit decay rates.

**Reference:** Glimm-Jaffe §17.5, Lemma 17.5.2.
-/

namespace IsingModel
namespace Ambient

/-! ## h=0 identity application to Step 5.7h -/

/-- **Per-pair `truncated2Infinite` exp bound from Simon-Lieb at h=0**
(`dist ≥ 2`).

At `h = 0`, `truncated2Infinite = correlationInfinite {i, j}`
(via `truncated2Infinite_h_zero`), so Step 5.7h's exp-form bound transfers
to `truncated2Infinite`. For `dist ≥ 2`:
`truncated2Infinite i j ≤ exp(-(simonLiebRate/2 · dist))`. -/
theorem truncated2Infinite_le_exp_neg_half_simonLiebRate_dist_of_dist_ge_two
    {d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {i j : Fin d → ℤ} (hdist : 2 ≤ latticeDistance d i j) :
    truncated2Infinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) i j
      ≤ Real.exp (-(simonLiebRate β J d / 2) *
          (latticeDistance d i j : ℝ)) := by
  rw [truncated2Infinite_h_zero]
  exact correlationInfinite_latticeGraph_le_exp_neg_half_simonLiebRate_dist_of_dist_ge_two
    hβJ hβJd_pos hβJd_le hdist

/-- **Ferromagnetic-form alias of the per-pair truncated2 bound**. -/
theorem truncated2Infinite_le_exp_neg_half_simonLiebRate_dist_of_ferromagnetic_dist_ge_two
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {i j : Fin d → ℤ} (hdist : 2 ≤ latticeDistance d i j) :
    truncated2Infinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) i j
      ≤ Real.exp (-(simonLiebRate β J d / 2) *
          (latticeDistance d i j : ℝ)) :=
  truncated2Infinite_le_exp_neg_half_simonLiebRate_dist_of_dist_ge_two
    (mul_nonneg hf.hβ.le hf.hJ) hβJd_pos hβJd_le hdist

/-! ## abs (truncated2Infinite) bound via nonnegativity (ferromagnetic) -/

/-- **`|truncated2Infinite| = truncated2Infinite` under ferromagnetic
nonnegativity**. -/
theorem abs_truncated2Infinite_eq_of_ferromagnetic
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    |truncated2Infinite (latticeGraph d) Λ p i j|
      = truncated2Infinite (latticeGraph d) Λ p i j :=
  abs_of_nonneg (truncated2Infinite_nonneg (latticeGraph d) Λ p hf i j)

/-- **`|truncated2Infinite| ≤ exp(-(simonLiebRate/2 · dist))` for dist ≥ 2,
ferromagnetic + high-temp** (combining absolute value rewrite with the
per-pair truncated2 bound). -/
theorem abs_truncated2Infinite_le_exp_neg_half_simonLiebRate_dist_of_ferromagnetic_dist_ge_two
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {i j : Fin d → ℤ} (hdist : 2 ≤ latticeDistance d i j) :
    |truncated2Infinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) i j|
      ≤ Real.exp (-(simonLiebRate β J d / 2) *
          (latticeDistance d i j : ℝ)) := by
  rw [abs_truncated2Infinite_eq_of_ferromagnetic _ _ hf]
  exact truncated2Infinite_le_exp_neg_half_simonLiebRate_dist_of_ferromagnetic_dist_ge_two
    hf hβJd_pos hβJd_le hdist

/-! ## dist = 1 fallback bound (abs ≤ 1) -/

/-- **`|truncated2Infinite| ≤ 1` (ferromagnetic)**. -/
theorem abs_truncated2Infinite_latticeGraph_le_one_of_ferromagnetic
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (i j : Fin d → ℤ) :
    |truncated2Infinite (latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) i j|
      ≤ 1 :=
  abs_truncated2Infinite_le_one (latticeGraph d) Λ
    (⟨J, 0, β⟩ : IsingParams ℝ) hf i j

/-- **Unified per-pair `truncated2Infinite` bound across all distinct `(i, j)`**.

For ferromagnetic + high-temp at `h = 0`:
`|truncated2Infinite i j| ≤ exp(simonLiebRate/2) · exp(-(simonLiebRate/2 · dist))`
for all `i ≠ j`. The constant `C := exp(simonLiebRate/2)` absorbs the
`dist = 1` adjacent case (where `|truncated2| ≤ 1 = exp(simonLiebRate/2 · 1)
· exp(-(simonLiebRate/2 · 1))` holds trivially) and dominates the
`dist ≥ 2` Step 5.7h bound. This establishes `HasExponentialDecay` at
rate `simonLiebRate / 2` with witness `C := exp(simonLiebRate/2)`. -/
theorem abs_truncated2Infinite_le_const_mul_exp_neg_half_simonLiebRate_dist
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {i j : Fin d → ℤ} (hij : i ≠ j) :
    |truncated2Infinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) i j|
      ≤ Real.exp (simonLiebRate β J d / 2) *
          Real.exp (-(simonLiebRate β J d / 2) *
            (latticeDistance d i j : ℝ)) := by
  have hSL_nn : 0 ≤ simonLiebRate β J d := by
    have hβJd_nn : 0 ≤ β * J * (2 * d) := hβJd_pos.le
    exact simonLiebRate_nonneg hβJd_nn hβJd_le
  have hdist_pos : 0 < latticeDistance d i j := by
    apply Nat.pos_of_ne_zero
    intro h_eq_zero
    exact hij ((IsingModel.latticeDistance_eq_zero_iff d i j).mp h_eq_zero)
  have hdist_ge_one : 1 ≤ latticeDistance d i j := hdist_pos
  by_cases h_eq_one : latticeDistance d i j = 1
  · -- dist = 1 case: |truncated2| ≤ 1 ≤ exp(s/2) · exp(-s/2 · 1)
    have h_le_one := abs_truncated2Infinite_latticeGraph_le_one_of_ferromagnetic
      (Ambient.cubicExhaustion d) hf i j
    have h_dist_cast : (latticeDistance d i j : ℝ) = 1 := by
      rw [h_eq_one]; norm_cast
    rw [h_dist_cast]
    have : Real.exp (simonLiebRate β J d / 2) *
        Real.exp (-(simonLiebRate β J d / 2) * 1) = 1 := by
      rw [mul_one]
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    rw [this]
    exact h_le_one
  · -- dist ≥ 2 case: use Step 5.7h
    have h_ge_two : 2 ≤ latticeDistance d i j := by omega
    have h_step :=
      abs_truncated2Infinite_le_exp_neg_half_simonLiebRate_dist_of_ferromagnetic_dist_ge_two
        hf hβJd_pos hβJd_le h_ge_two
    have h_exp_pos : 0 < Real.exp (simonLiebRate β J d / 2) := Real.exp_pos _
    have h_exp_ge_one : 1 ≤ Real.exp (simonLiebRate β J d / 2) := by
      apply Real.one_le_exp
      linarith
    calc |truncated2Infinite (latticeGraph d) (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) i j|
        ≤ Real.exp (-(simonLiebRate β J d / 2) *
            (latticeDistance d i j : ℝ)) := h_step
      _ = 1 * Real.exp (-(simonLiebRate β J d / 2) *
            (latticeDistance d i j : ℝ)) := by rw [one_mul]
      _ ≤ Real.exp (simonLiebRate β J d / 2) *
          Real.exp (-(simonLiebRate β J d / 2) *
            (latticeDistance d i j : ℝ)) := by
        apply mul_le_mul_of_nonneg_right h_exp_ge_one
        exact (Real.exp_pos _).le

/-! ## HasExponentialDecay from Simon-Lieb at h=0 -/

/-- **`HasExponentialDecay` established from Simon-Lieb at `h = 0`**
(ferromagnetic high-temp).

For `Ferromagnetic ⟨J, 0, β⟩` + strict high-temp `0 < β·J·(2d) ≤ 1`:
`HasExponentialDecay d (cubicExhaustion d) ⟨J, 0, β⟩ (simonLiebRate β J d / 2)`
with witness `C := exp(simonLiebRate β J d / 2)`. -/
theorem hasExponentialDecay_of_simonLieb_ferromagnetic_high_temp
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1) :
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (simonLiebRate β J d / 2) := by
  refine ⟨Real.exp (simonLiebRate β J d / 2), (Real.exp_pos _).le, ?_⟩
  intro i j hij
  exact abs_truncated2Infinite_le_const_mul_exp_neg_half_simonLiebRate_dist
    hf hβJd_pos hβJd_le hij

/-! ## Substantive tsum bound: connect to existing tsum_truncated2Infinite_prod_le -/

/-- **Substantive tsum bound at h=0 from Simon-Lieb** (existential form).

Composes `hasExponentialDecay_of_simonLieb_ferromagnetic_high_temp` with
`tsum_truncated2Infinite_prod_le`: under ferromagnetic high-temp,
there exist explicit positive constants `K, M` such that for all `x, y`
the tsum product is bounded by `K · exp(-(M · d(x, y)))`. -/
theorem exists_tsum_truncated2Infinite_prod_le_of_simonLieb_ferromagnetic_high_temp
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) x z *
            truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) y z
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) := by
  have hβJd_le : β * J * (2 * d) ≤ 1 := hβJd_lt.le
  have hSL_pos : 0 < simonLiebRate β J d :=
    simonLiebRate_pos hβJd_pos hβJd_lt
  have hSL_half_pos : 0 < simonLiebRate β J d / 2 := by linarith
  set α := simonLiebRate β J d / 2 with hα_def
  set C := Real.exp α with hC_def
  have hα_pos : 0 < α := hSL_half_pos
  have hC_nn : 0 ≤ C := (Real.exp_pos _).le
  have h_bound' : ∀ i j : Fin d → ℤ, i ≠ j →
      |truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) i j|
        ≤ C * Real.exp (-α * (latticeDistance d i j : ℝ)) := fun i j hij =>
      abs_truncated2Infinite_le_const_mul_exp_neg_half_simonLiebRate_dist
        (J := J) (β := β) (d := d) hf hβJd_pos hβJd_le hij
  refine ⟨(C + 1) ^ 2 *
            (2 * ∑' z : Fin d → ℤ,
              Real.exp (-(α / 2) * (latticeDistance d 0 z : ℝ))), α / 4,
          ?_, by linarith, ?_⟩
  · have h_K_factor1_nn : (0 : ℝ) ≤ (C + 1) ^ 2 := sq_nonneg _
    have h_tsum_nn : 0 ≤ ∑' z : Fin d → ℤ,
        Real.exp (-(α / 2) * (latticeDistance d 0 z : ℝ)) :=
      tsum_nonneg (fun z => (Real.exp_pos _).le)
    have h_K_factor2_nn : (0 : ℝ) ≤ 2 * ∑' z : Fin d → ℤ,
        Real.exp (-(α / 2) * (latticeDistance d 0 z : ℝ)) := by
      have h2 : (0 : ℝ) ≤ 2 := by norm_num
      exact mul_nonneg h2 h_tsum_nn
    exact mul_nonneg h_K_factor1_nn h_K_factor2_nn
  · intro x y
    have h_tsum := tsum_truncated2Infinite_prod_le
      hf.hJ hf.hβ hα_pos hC_nn h_bound' x y
    have h_rate_eq : -(α / 2) * (latticeDistance d x y : ℝ) / 2 =
        -(α / 4) * (latticeDistance d x y : ℝ) := by ring
    have h_exp_eq : Real.exp (-(α / 2) * (latticeDistance d x y : ℝ) / 2) =
        Real.exp (-(α / 4) * (latticeDistance d x y : ℝ)) := by
      rw [h_rate_eq]
    rw [h_exp_eq] at h_tsum
    exact h_tsum

end Ambient
end IsingModel
