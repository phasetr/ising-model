import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature.PathLowerBound

/-!
# Lattice mass at high temperature split — Step 115 upper bound on the lattice mass

Part of the split high-temperature lattice-mass layer (Issue #1850).
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## §17.5 Step 115: Upper bound on the lattice mass -/

/-- For `d ≥ 1` and `n : ℕ`, the axis point `fun i : Fin d => if i.val = 0 then n else 0`
is at `latticeDistance d 0 r = n` from the origin. -/
private lemma latticeDistance_coord_eq {d : ℕ} (hd : 0 < d) (n : ℕ) :
    IsingModel.latticeDistance d 0 (fun i : Fin d => if i.val = 0 then (n : ℤ) else 0) = n := by
  unfold IsingModel.latticeDistance
  simp only [Pi.zero_apply, zero_sub, Int.natAbs_neg]
  rw [Finset.sum_eq_single ⟨0, hd⟩
      (fun j _ hj => by simp [show j.val ≠ 0 from fun h => hj (Fin.ext h)])
      (fun h => absurd (Finset.mem_univ _) h)]
  simp

open IsingModel in
/-- **Upper bound on the lattice mass** (GJ §17.5 pp. 304–306):
for `d ≥ 1`, `J > 0`, `β > 0` at `h = 0`,
`latticeMass d (cubicExhaustion d) ⟨J,0,β⟩ ≤ ENNReal.ofReal (-log(tanh(βJ)))`.

Combined with the lower bound from Step 111, this gives the two-sided bound
`-log(βJD) ≤ latticeMass ≤ -log(tanh(βJ))` in the high-temperature regime.

Proof: for each `α : NNReal` with `HasExponentialDecay` at rate `α` and witness `C`, we show
`α ≤ -log(tanh(βJ))` by contradiction. Set `ε := log(tanh(βJ)) + α > 0`. By Archimedean,
find `n₀ : ℕ` with `C < ε * n₀`. The axis point `r_n = (n₀,0,...,0)` satisfies
`dist(0, r_n) = n₀`. Step 114 gives `tanh(βJ)^n₀ ≤ twoPointFunction d p r_n = |truncated2|
≤ C * exp(-α * n₀)`. Rearranging: `exp(ε * n₀) ≤ C`. But `exp(ε * n₀) ≥ ε * n₀ + 1 > C`.
Contradiction.

Reference: Glimm–Jaffe §17.5 pp. 304–306 (2nd ed.). -/
theorem latticeMass_le_neg_log_tanh_betaJ
    {d : ℕ} (hd : 0 < d) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    latticeMass d (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ ENNReal.ofReal (-Real.log (Real.tanh (β * J))) := by
  have htanh_pos : 0 < Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ hJ)) (Real.cosh_pos _)
  unfold latticeMass
  apply sSup_le
  rintro b ⟨α, hα_dec, rfl⟩
  change (↑α : ENNReal) ≤ ENNReal.ofReal (-Real.log (Real.tanh (β * J)))
  obtain ⟨C, hC, hbound⟩ := hα_dec
  suffices h_le : (α : ℝ) ≤ -Real.log (Real.tanh (β * J)) by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal h_le
  by_contra h_alpha_gt
  simp only [not_le] at h_alpha_gt
  set ε := Real.log (Real.tanh (β * J)) + (α : ℝ) with hε_def
  have hε_pos : 0 < ε := by linarith
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (C / ε)
  have hn₀_ε : C < ε * ↑n₀ := by
    have h := (div_lt_iff₀ hε_pos).mp hn₀
    rwa [mul_comm (↑n₀ : ℝ) ε] at h
  have hn₀_pos : 0 < n₀ :=
    Nat.cast_pos.mp ((div_nonneg hC hε_pos.le).trans_lt hn₀)
  set r_n := fun i : Fin d => if i.val = 0 then (n₀ : ℤ) else 0
  have hr_ne : r_n ≠ 0 := by
    intro heq
    have h0 : (n₀ : ℤ) = 0 := by
      have := congr_fun heq ⟨0, hd⟩
      simp only [Pi.zero_apply, r_n, if_pos rfl] at this
      exact this
    exact absurd h0 (by exact_mod_cast hn₀_pos.ne')
  have hdist : latticeDistance d 0 r_n = n₀ := latticeDistance_coord_eq hd n₀
  have h_lb : Real.tanh (β * J) ^ n₀ ≤ twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) r_n :=
    hdist ▸ twoPointFunction_ge_tanh_betaJ_pow_dist hJ.le hβ hr_ne
  have h_ub : twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) r_n ≤
      C * Real.exp (-(↑α : ℝ) * ↑n₀) := by
    have h' := hbound 0 r_n (Ne.symm hr_ne)
    simp only [truncated2Infinite_h_zero] at h'
    rw [abs_of_nonneg (correlationInfinite_nonneg_of_hβJ (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (mul_nonneg hβ.le hJ.le) {0, r_n}),
        ← twoPointFunction_apply, hdist] at h'
    exact h'
  have h_combined : Real.tanh (β * J) ^ n₀ ≤ C * Real.exp (-(↑α : ℝ) * ↑n₀) :=
    h_lb.trans h_ub
  have h_exp_le_C : Real.exp (ε * ↑n₀) ≤ C := by
    have key : Real.exp (ε * ↑n₀) =
        Real.tanh (β * J) ^ n₀ * Real.exp ((↑α : ℝ) * ↑n₀) := by
      rw [hε_def, add_mul, Real.exp_add,
          show Real.log (Real.tanh (β * J)) * ↑n₀ = ↑n₀ * Real.log (Real.tanh (β * J))
            from mul_comm _ _,
          ← Real.log_pow (Real.tanh (β * J)) n₀,
          Real.exp_log (pow_pos htanh_pos n₀)]
    rw [key]
    calc Real.tanh (β * J) ^ n₀ * Real.exp ((↑α : ℝ) * ↑n₀)
        ≤ C * Real.exp (-(↑α : ℝ) * ↑n₀) * Real.exp ((↑α : ℝ) * ↑n₀) :=
            mul_le_mul_of_nonneg_right h_combined (Real.exp_pos _).le
      _ = C := by
            rw [mul_assoc, ← Real.exp_add]
            have h0 : -(↑α : ℝ) * ↑n₀ + (↑α : ℝ) * ↑n₀ = 0 := by ring
            rw [h0, Real.exp_zero, mul_one]
  linarith [Real.add_one_le_exp (ε * ↑n₀)]

/-- **Lattice mass two-sided bound** (Step 153, GJ §17.5 pp. 304–306):
in the high-temperature regime (`d ≥ 1`, `0 < J`, `0 < β`, `βJ·2d < 1`):
`ENNReal.ofReal (-log(βJ·2d)) ≤ latticeMass ≤ ENNReal.ofReal (-log(tanh(βJ)))`.

Bundles `latticeMass_ge_neg_log_of_high_temp` (lower, Step 152) and
`latticeMass_le_neg_log_tanh_betaJ` (upper, Step 115) into one statement. -/
theorem latticeMass_two_sided_bound
    {d : ℕ} (hd : 0 < d) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) :
    ENNReal.ofReal (-Real.log (β * J * ↑(2 * d))) ≤
    latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) ≤
    ENNReal.ofReal (-Real.log (Real.tanh (β * J))) :=
  ⟨latticeMass_ge_neg_log_of_high_temp hd (mul_pos hβ hJ) hlt,
   latticeMass_le_neg_log_tanh_betaJ hd hJ hβ⟩



end Ambient
end IsingModel
