import IsingModel.Concrete.LatticeGraphCorrelation.SimonLiebDistanceDecay

/-!
# Simon-Lieb distance-decay ferromagnetic aliases bundle

GJ-proposition-unit bundle of ferromagnetic-form aliases for the Simon-Lieb
distance-decay infrastructure (PRs #3178, #3179):

- `correlationInfinite_latticeGraph_le_betaJ_two_d_pow_of_dist_gt`
- `correlationInfinite_latticeGraph_le_exp_neg_simonLiebRate_pow_of_dist_gt`
- `correlationInfinite_latticeGraph_le_exp_neg_half_simonLiebRate_dist_of_dist_ge_two`

These wrappers take the `Ferromagnetic ⟨J, 0, β⟩` predicate directly.

**Reference:** Glimm--Jaffe §5.1 pp. 76-79; §17.5 pp. 311-312.
-/

namespace IsingModel
namespace Ambient

/-! ## Ferromagnetic-form Simon-Lieb aliases -/

/-- **Simon-Lieb power decay from `Ferromagnetic ⟨J, 0, β⟩`**. -/
theorem correlationInfinite_latticeGraph_le_betaJ_two_d_pow_of_ferromagnetic_dist_gt
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (n : ℕ) (i j : Fin d → ℤ) (hdist : n + 1 ≤ latticeDistance d i j) :
    correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ (β * J * (2 * d)) ^ n :=
  correlationInfinite_latticeGraph_le_betaJ_two_d_pow_of_dist_gt
    (mul_nonneg hf.hβ.le hf.hJ) n i j hdist

/-- **Simon-Lieb exp-form decay from `Ferromagnetic ⟨J, 0, β⟩`**. -/
theorem correlationInfinite_latticeGraph_le_exp_neg_simonLiebRate_pow_of_ferromagnetic_dist_gt
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d))
    (n : ℕ) (i j : Fin d → ℤ) (hdist : n + 1 ≤ latticeDistance d i j) :
    correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ Real.exp (-(simonLiebRate β J d) * (n : ℝ)) :=
  correlationInfinite_latticeGraph_le_exp_neg_simonLiebRate_pow_of_dist_gt
    (mul_nonneg hf.hβ.le hf.hJ) hβJd_pos n i j hdist

/-- **Simon-Lieb dist ≥ 2 M/2 form from `Ferromagnetic ⟨J, 0, β⟩`**. -/
theorem
correlationInfinite_latticeGraph_le_exp_neg_half_simonLiebRate_dist_of_ferromagnetic_dist_ge_two
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {i j : Fin d → ℤ} (hdist : 2 ≤ latticeDistance d i j) :
    correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ Real.exp (-(simonLiebRate β J d / 2) *
          (latticeDistance d i j : ℝ)) :=
  correlationInfinite_latticeGraph_le_exp_neg_half_simonLiebRate_dist_of_dist_ge_two
    (mul_nonneg hf.hβ.le hf.hJ) hβJd_pos hβJd_le hdist

/-! ## simonLiebRate positivity / nonneg under ferromagnetic + high-temp -/

/-- **`simonLiebRate β J d ≥ 0` from `Ferromagnetic ⟨J, 0, β⟩` + `β·J·2d ≤ 1`
+ `β·J·2d ≥ 0`**. -/
theorem simonLiebRate_nonneg_of_ferromagnetic_high_temp
    {β J : ℝ} {d : ℕ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_nn : 0 ≤ β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1) :
    0 ≤ simonLiebRate β J d := by
  have := hf
  exact simonLiebRate_nonneg hβJd_nn hβJd_le

/-- **`simonLiebRate β J d > 0` from `Ferromagnetic ⟨J, 0, β⟩` + strict
high-temp**. -/
theorem simonLiebRate_pos_of_ferromagnetic_strict_high_temp
    {β J : ℝ} {d : ℕ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1) :
    0 < simonLiebRate β J d := by
  have := hf
  exact simonLiebRate_pos hβJd_pos hβJd_lt

/-- **High-temperature betaJ_two_d ≥ 0 from `Ferromagnetic ⟨J, 0, β⟩`**. -/
theorem ferromagnetic_implies_betaJ_two_d_nonneg
    {J β : ℝ} {d : ℕ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    0 ≤ β * J * (2 * d) :=
  mul_nonneg (mul_nonneg hf.hβ.le hf.hJ) (by positivity)

/-! ## High-temperature regime alias -/

/-- **High-temperature `(β·J·2d) ∈ [0, 1)` from `Ferromagnetic` + `< 1`
hypothesis**. -/
theorem betaJ_two_d_mem_Ico_of_ferromagnetic_lt_one
    {β J : ℝ} {d : ℕ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_lt : β * J * (2 * d) < 1) :
    β * J * (2 * d) ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨ferromagnetic_implies_betaJ_two_d_nonneg hf, hβJd_lt⟩

/-- **`simonLiebRate` ≥ 0 from `Ferromagnetic` + `β·J·2d ≤ 1`** (helper
combining the nonneg derivation). -/
theorem simonLiebRate_nonneg_of_ferromagnetic_le_one
    {β J : ℝ} {d : ℕ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_le : β * J * (2 * d) ≤ 1) :
    0 ≤ simonLiebRate β J d :=
  simonLiebRate_nonneg_of_ferromagnetic_high_temp hf
    (ferromagnetic_implies_betaJ_two_d_nonneg hf) hβJd_le

end Ambient
end IsingModel
