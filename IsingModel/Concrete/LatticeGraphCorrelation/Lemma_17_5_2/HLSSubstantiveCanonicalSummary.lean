import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferSummability
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature.ExpDecay
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation
import IsingModel.Concrete.LatticeGraphCorrelation.SimonLiebDistanceDecay
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPointTruncatedInfiniteTrivialSlice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPointTruncatedInfiniteBounds

/-!
# Substantive HLS canonical summary API + short aliases

GJ-proposition-unit canonical summary API for the full-rate substantive HLS
sum bound chain.

Provides the simplest stable entry points for the strongest existing-rate path
(#3202, via existing `hasExponentialDecay_of_high_temp`) and the underlying
existing-rate HLS bridges formerly housed in the retired
`HLSExistingHasExponentialDecayBridges` wrapper module. It also retains the
older Simon-Lieb half-rate path formerly housed in the retired
`HLSSubstantiveBundle` wrapper module.

**Reference:** Glimm-Jaffe §17.5 Lemma 17.5.2.
-/

namespace IsingModel
namespace Ambient

/-! ## Simon-Lieb half-rate to substantive HLS sum bridges -/

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

/-! ## Existing HasExponentialDecay to substantive HLS sum bridges -/

/-- **Substantive tsum bound at h=0 from the existing high-temp
HasExponentialDecay** (FULL rate `-log(β·J·(2d))`, stronger than #3199). -/
theorem exists_tsum_truncated2Infinite_prod_le_of_existing_high_temp
    {d : ℕ} {β J : ℝ}
    (hβJ : 0 ≤ β * J) (hβJd_pos : 0 < β * J * (2 * d))
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (hβ : 0 < β) (hJ : 0 ≤ J) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) x z *
            truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) y z
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) := by
  obtain ⟨C, hC_nn, hbound⟩ := hasExponentialDecay_of_high_temp hβJ hβJd_lt
  set α := -Real.log (β * J * ↑(2 * d)) with hα_def
  have hα_pos : 0 < α := by
    rw [hα_def]
    apply neg_pos.mpr
    have h_cast : β * J * ↑(2 * d) = β * J * (2 * d) := by push_cast; ring
    rw [h_cast]
    exact Real.log_neg hβJd_pos (by rw [← h_cast]; exact hβJd_lt)
  have hα_half_pos : 0 < α / 2 := by linarith
  refine ⟨(C + 1) ^ 2 *
            (2 * ∑' z : Fin d → ℤ,
              Real.exp (-(α / 2) * (latticeDistance d 0 z : ℝ))), α / 4,
          ?_, by linarith, ?_⟩
  · have h_K_factor1_nn : (0 : ℝ) ≤ (C + 1) ^ 2 := sq_nonneg _
    have h_tsum_nn : 0 ≤ ∑' z : Fin d → ℤ,
        Real.exp (-(α / 2) * (latticeDistance d 0 z : ℝ)) :=
      tsum_nonneg (fun _ => (Real.exp_pos _).le)
    have h_K_factor2_nn : (0 : ℝ) ≤ 2 * ∑' z : Fin d → ℤ,
        Real.exp (-(α / 2) * (latticeDistance d 0 z : ℝ)) :=
      mul_nonneg (by norm_num) h_tsum_nn
    exact mul_nonneg h_K_factor1_nn h_K_factor2_nn
  · intro x y
    have h_tsum := tsum_truncated2Infinite_prod_le
      hJ hβ hα_pos hC_nn hbound x y
    have h_rate_eq : -(α / 2) * (latticeDistance d x y : ℝ) / 2 =
        -(α / 4) * (latticeDistance d x y : ℝ) := by ring
    have h_exp_eq : Real.exp (-(α / 2) * (latticeDistance d x y : ℝ) / 2) =
        Real.exp (-(α / 4) * (latticeDistance d x y : ℝ)) := by rw [h_rate_eq]
    rw [h_exp_eq] at h_tsum
    exact h_tsum

/-- **Ferromagnetic-form alias** of the existing-rate substantive bound. -/
theorem exists_tsum_truncated2Infinite_prod_le_of_existing_ferromagnetic_high_temp
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) x z *
            truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) y z
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) :=
  exists_tsum_truncated2Infinite_prod_le_of_existing_high_temp
    (mul_nonneg hf.hβ.le hf.hJ) hβJd_pos hβJd_lt hf.hβ hf.hJ

/-- **Correlation-form via h=0 identity**. -/
theorem exists_tsum_correlationInfinite_pair_product_le_of_existing_ferromagnetic
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
    exists_tsum_truncated2Infinite_prod_le_of_existing_ferromagnetic_high_temp
      hf hβJd_pos hβJd_lt
  refine ⟨K, M, hK_nn, hM_pos, ?_⟩
  intro x y
  have h_summand_eq : ∀ z : Fin d → ℤ,
      truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z *
      truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) y z =
      correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
      correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {y, z} := fun z => by
    rw [truncated2Infinite_latticeGraph_h_zero d J β x z,
        truncated2Infinite_latticeGraph_h_zero d J β y z]
  have h_tsum_eq : (∑' z : Fin d → ℤ,
      truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z *
      truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) y z) =
      ∑' z : Fin d → ℤ,
        correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
        correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {y, z} := by
    congr 1
    funext z
    exact h_summand_eq z
  rw [← h_tsum_eq]
  exact h_bound x y

/-- **`-log(β·J·(2d)) > 0` from strict high-temp**. -/
theorem neg_log_betaJ_two_d_pos_of_strict_high_temp
    {β J : ℝ} {d : ℕ}
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 < -Real.log (β * J * ↑(2 * d)) := by
  apply neg_pos.mpr
  have hβJd_cast : β * J * ↑(2 * d) = β * J * (2 * d) := by push_cast; ring
  rw [hβJd_cast] at hβJd_lt ⊢
  exact Real.log_neg hβJd_pos hβJd_lt

/-- **`1 / (1 - β·J·(2d)) > 0` from strict high-temp**. -/
theorem one_div_one_sub_pos_of_strict_high_temp
    {β J : ℝ} {d : ℕ}
    (hβJd_lt : β * J * (2 * d) < 1) :
    (0 : ℝ) < 1 / (1 - β * J * (2 * d)) := by
  have h_denom_pos : (0 : ℝ) < 1 - β * J * (2 * d) := by linarith
  exact div_pos zero_lt_one h_denom_pos

/-! ## Short canonical entry points (full-rate / strongest) -/

/-- **Canonical substantive HLS sum bound** (full-rate, strongest, ferromagnetic).
Short alias for `exists_tsum_correlationInfinite_pair_product_le_of_existing_ferromagnetic`. -/
theorem hls_substantive_bound
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) :=
  exists_tsum_correlationInfinite_pair_product_le_of_existing_ferromagnetic
    hf hβJd_pos hβJd_lt

/-- **Canonical cluster property** (ferromagnetic + strict high-temp). -/
theorem hls_cluster_property
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  have hα_pos := neg_log_betaJ_two_d_pos_of_strict_high_temp hβJd_pos hβJd_lt
  have h_decay :=
    hasExponentialDecay_of_high_temp (mul_nonneg hf.hβ.le hf.hJ) hβJd_lt
  clusterProperty_latticeGraph_of_HasExponentialDecay d
    (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hα_pos h_decay

/-- **Canonical per-site cofinite tendsto** (truncated2 form). -/
theorem hls_tendsto_truncated2
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    Filter.Tendsto (fun j : Fin d → ℤ =>
        truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) i j) Filter.cofinite (nhds 0) :=
  hls_cluster_property hf hβJd_pos hβJd_lt i

/-- **Canonical per-site cofinite tendsto** (correlation form at h=0). -/
theorem hls_tendsto_correlation
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    Filter.Tendsto (fun j : Fin d → ℤ =>
        correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}) Filter.cofinite (nhds 0) :=
  by
    have h_t2 := hls_tendsto_truncated2 hf hβJd_pos hβJd_lt i
    have h_eq : (fun j : Fin d → ℤ =>
        truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) i j) =
        (fun j : Fin d → ℤ =>
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}) := by
      funext j
      exact truncated2Infinite_latticeGraph_h_zero d J β i j
    rw [h_eq] at h_t2
    exact h_t2

/-! ## Anchor canonical entry points -/

/-- **Canonical zero-anchor substantive HLS bound** at `(0, 0)`. -/
theorem hls_substantive_bound_zero_anchor
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∑' z : Fin d → ℤ,
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {0, z} *
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {0, z}
      ≤ K * Real.exp (-M * (latticeDistance d 0 0 : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
    hls_substantive_bound hf hβJd_pos hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, h_bound 0 0⟩

/-- **Canonical diagonal substantive HLS bound** at `(x₀, x₀)`. -/
theorem hls_substantive_bound_diagonal
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (x₀ : Fin d → ℤ) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∑' z : Fin d → ℤ,
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z}
      ≤ K * Real.exp (-M * (latticeDistance d x₀ x₀ : ℝ)) :=
  by
    obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
      hls_substantive_bound hf hβJd_pos hβJd_lt
    exact ⟨K, M, hK_nn, hM_pos, h_bound x₀ x₀⟩

/-- **Canonical swapped-anchor substantive HLS bound** at `(y₀, x₀)`. -/
theorem hls_substantive_bound_swap
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (x₀ y₀ : Fin d → ℤ) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∑' z : Fin d → ℤ,
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z} *
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z}
      ≤ K * Real.exp (-M * (latticeDistance d y₀ x₀ : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
    hls_substantive_bound hf hβJd_pos hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, h_bound y₀ x₀⟩

/-- **Canonical antipode-anchor substantive HLS bound** at `(v, -v)`. -/
theorem hls_substantive_bound_antipode
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (v : Fin d → ℤ) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∑' z : Fin d → ℤ,
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {v, z} *
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {-v, z}
      ≤ K * Real.exp (-M * (latticeDistance d v (-v) : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
    hls_substantive_bound hf hβJd_pos hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, h_bound v (-v)⟩

/-! ## Witness canonical entry points -/

/-- **Canonical `K ≥ 0`, `M > 0` extraction** from the substantive HLS bound. -/
theorem hls_exists_K_M_substantive_bound
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M :=
  let ⟨K, M, hK_nn, hM_pos, _⟩ := hls_substantive_bound hf hβJd_pos hβJd_lt
  ⟨K, M, hK_nn, hM_pos⟩

/-! ## HasExponentialDecay canonical -/

/-- **Canonical HasExponentialDecay** at the strongest rate `-log(β·J·(2d))`. -/
theorem hls_hasExponentialDecay
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * ↑(2 * d))) :=
  hasExponentialDecay_of_high_temp (mul_nonneg hf.hβ.le hf.hJ) hβJd_lt

/-- **Canonical existential positive rate HasExponentialDecay witness**. -/
theorem hls_exists_pos_rate_decay
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ α : ℝ, 0 < α ∧
      HasExponentialDecay d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) α :=
  ⟨-Real.log (β * J * ↑(2 * d)),
    neg_log_betaJ_two_d_pos_of_strict_high_temp hβJd_pos hβJd_lt,
    hls_hasExponentialDecay hf hβJd_lt⟩

/-! ## Canonical positive rate accessor -/

/-- **Canonical positive rate `-log(β·J·(2d))`**. -/
theorem hls_canonical_rate_pos
    {β J : ℝ} {d : ℕ}
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 : ℝ) < -Real.log (β * J * ↑(2 * d)) :=
  neg_log_betaJ_two_d_pos_of_strict_high_temp hβJd_pos hβJd_lt

/-- **Canonical HLS tsum rate `-log(β·J·(2d))/4` positivity helper**. -/
theorem hls_canonical_tsum_rate_pos
    {β J : ℝ} {d : ℕ}
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 : ℝ) < -Real.log (β * J * ↑(2 * d)) / 4 := by
  have h := hls_canonical_rate_pos hβJd_pos hβJd_lt
  linarith

end Ambient
end IsingModel
