import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature.ExpDecay

/-!
# Lattice mass at high temperature split — Steps 111-112 positive lattice mass and antitonicity

Part of the split high-temperature lattice-mass layer (Issue #1850).
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## §17.5 Step 111: Positive lattice mass at high temperature -/

open IsingModel in
/-- **Positive lattice mass at high temperature** (GJ §17.5 pp. 304–306):
for `0 < βJ` and `βJD < 1` (D = 2d), the lattice mass is positive,
i.e., the correlation length is finite.

For `d = 0`: `Fin 0 → ℤ` is a singleton, `HasExponentialDecay` holds
vacuously for any rate; `latticeMass ≥ 1 > 0`.
For `d ≥ 1`: `hasExponentialDecay_of_high_temp` (Step 110) gives rate
`α₀ = -log(βJD) > 0` (since `0 < βJD < 1`); `latticeMass ≥ α₀ > 0`.

Reference: Glimm–Jaffe §17.5 pp. 304–306. -/
theorem latticeMass_pos_of_high_temp
    {d : ℕ} {β J : ℝ} (hβJ : 0 < β * J)
    (hlt : β * J * ↑(2 * d) < 1) :
    0 < latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) := by
  unfold latticeMass
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- d = 0: Fin 0 → ℤ is a singleton, all pairs i ≠ j are vacuous
    have h_vac : HasExponentialDecay 0 (cubicExhaustion 0)
        (⟨J, 0, β⟩ : IsingParams ℝ) (1 : ℝ) :=
      ⟨0, le_refl _, fun i j hij =>
        absurd (funext (fun x => Fin.elim0 x)) hij⟩
    exact lt_of_lt_of_le (by norm_num)
      (le_sSup (show ((1 : NNReal) : ENNReal) ∈ (fun α : NNReal => (α : ENNReal)) ''
          {α : NNReal | HasExponentialDecay 0 (cubicExhaustion 0)
              (⟨J, 0, β⟩ : IsingParams ℝ) (α : ℝ)} from ⟨1, h_vac, rfl⟩))
  · -- d ≥ 1: α₀ = -log(βJD) > 0
    have hβJD_pos : 0 < β * J * ↑(2 * d) :=
      mul_pos hβJ (Nat.cast_pos.mpr (by omega))
    have hα_pos : 0 < -Real.log (β * J * ↑(2 * d)) :=
      neg_pos.mpr (Real.log_neg hβJD_pos hlt)
    set α₀ : NNReal := ⟨-Real.log (β * J * ↑(2 * d)), le_of_lt hα_pos⟩
    have h_mem : (α₀ : ENNReal) ∈ (fun α : NNReal => (α : ENNReal)) ''
        {α : NNReal | HasExponentialDecay d (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) (α : ℝ)} :=
      ⟨α₀, hasExponentialDecay_of_high_temp hβJ.le hlt, rfl⟩
    apply lt_of_lt_of_le _ (le_sSup h_mem)
    have : (0 : ℝ) < (α₀ : ℝ) := hα_pos
    exact_mod_cast this

/-- **Lattice mass lower bound in high-temperature regime** (Step 152, GJ §17.5):
for `d ≥ 1`, `0 < βJ`, and `βJ·2d < 1`:
`ENNReal.ofReal (-log(βJ·2d)) ≤ latticeMass d (cubicExhaustion d) ⟨J,0,β⟩`.

The rate `α₀ = -log(βJD)` (with `D = 2d`) from Step 110 is in the defining set of
`latticeMass`, so `latticeMass ≥ α₀`. This makes the lower bound from `latticeMass_pos_of_high_temp`
(Step 111) explicit: the exponential decay rate `α₀` is a concrete lower bound for the mass.

Reference: Glimm–Jaffe §17.5 pp. 304–306. -/
theorem latticeMass_ge_neg_log_of_high_temp
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ} (hβJ : 0 < β * J)
    (hlt : β * J * ↑(2 * d) < 1) :
    ENNReal.ofReal (-Real.log (β * J * ↑(2 * d))) ≤
    latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) := by
  unfold latticeMass
  have hβJD_pos : 0 < β * J * ↑(2 * d) :=
    mul_pos hβJ (Nat.cast_pos.mpr (by omega))
  have hα_pos : 0 < -Real.log (β * J * ↑(2 * d)) :=
    neg_pos.mpr (Real.log_neg hβJD_pos hlt)
  set α₀ : NNReal := ⟨-Real.log (β * J * ↑(2 * d)), le_of_lt hα_pos⟩
  apply le_sSup
  exact ⟨α₀, hasExponentialDecay_of_high_temp hβJ.le hlt,
         (ENNReal.ofReal_eq_coe_nnreal hα_pos.le).symm⟩

/-! ## §17.5 Step 112: Lattice mass antitonicity in β and J -/

/-- **Lattice mass antitone in β** at h = 0 (GJ §17.1 pp. 304–306):
for fixed `J ≥ 0` and `0 < β₁ ≤ β₂`, the lattice mass satisfies
`latticeMass(β₂) ≤ latticeMass(β₁)`.

Physics: higher temperature (lower β) → stronger high-temp regime
→ faster exponential decay → larger mass (shorter correlation length).

Proof: `HasExponentialDecay(β₂, α)` with witness `C` implies the same
for `β₁` using `truncated2Infinite_h_zero` + GKS-II β-monotonicity
(`correlationInfinite_monotone_beta`, GJ Prop 4.2.4) + GKS-I nonnegativity
(`correlationInfinite_nonneg_of_hβJ`).

Reference: Glimm–Jaffe §17.1 pp. 304–306; §4.2 Prop 4.2.4 (β-monotonicity). -/
theorem latticeMass_antitone_beta
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂) :
    latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
    latticeMass d Λ (⟨J, 0, β₁⟩ : IsingParams ℝ) := by
  unfold latticeMass
  apply sSup_le_sSup
  intro a ha
  obtain ⟨α, hα_decay, rfl⟩ := ha
  obtain ⟨C, hC, hbound⟩ := hα_decay
  refine ⟨α, ⟨C, hC, fun i j hij => ?_⟩, rfl⟩
  simp only [truncated2Infinite_h_zero] at hbound ⊢
  have hnn₁ : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β₁⟩ : IsingParams ℝ) {i, j} :=
    correlationInfinite_nonneg_of_hβJ (IsingModel.latticeGraph d) Λ
      (mul_nonneg hβ₁.le hJ) {i, j}
  have hnn₂ : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β₂⟩ : IsingParams ℝ) {i, j} :=
    correlationInfinite_nonneg_of_hβJ (IsingModel.latticeGraph d) Λ
      (mul_nonneg (hβ₁.le.trans hβ₁₂) hJ) {i, j}
  rw [abs_of_nonneg hnn₁]
  calc correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β₁⟩ : IsingParams ℝ) {i, j}
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) {i, j} :=
        correlationInfinite_monotone_beta (IsingModel.latticeGraph d) Λ hJ (le_refl 0) {i, j}
          (Set.mem_Ioi.mpr hβ₁) (Set.mem_Ioi.mpr (hβ₁.trans_le hβ₁₂)) hβ₁₂
      _ ≤ C * Real.exp (-↑α * (IsingModel.latticeDistance d i j : ℝ)) := by
          have hb := hbound i j hij
          rwa [abs_of_nonneg hnn₂] at hb

/-- **Lattice mass antitone in J** at h = 0 (GJ §17.1 pp. 304–306):
for fixed `β > 0` and `0 ≤ J₁ ≤ J₂`, the lattice mass satisfies
`latticeMass(J₂) ≤ latticeMass(J₁)`.

Same argument as `latticeMass_antitone_beta` using GKS-II J-monotonicity
(`correlationInfinite_monotone_J`, GJ Prop 4.2.3) instead.

Reference: Glimm–Jaffe §17.1 pp. 304–306; §4.2 Prop 4.2.3 (J-monotonicity). -/
theorem latticeMass_antitone_J
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hJ₁₂ : J₁ ≤ J₂)
    {β : ℝ} (hβ : 0 < β) :
    latticeMass d Λ (⟨J₂, 0, β⟩ : IsingParams ℝ) ≤
    latticeMass d Λ (⟨J₁, 0, β⟩ : IsingParams ℝ) := by
  unfold latticeMass
  apply sSup_le_sSup
  intro a ha
  obtain ⟨α, hα_decay, rfl⟩ := ha
  obtain ⟨C, hC, hbound⟩ := hα_decay
  refine ⟨α, ⟨C, hC, fun i j hij => ?_⟩, rfl⟩
  simp only [truncated2Infinite_h_zero] at hbound ⊢
  have hnn₁ : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J₁, 0, β⟩ : IsingParams ℝ) {i, j} :=
    correlationInfinite_nonneg_of_hβJ (IsingModel.latticeGraph d) Λ
      (mul_nonneg hβ.le hJ₁) {i, j}
  have hnn₂ : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J₂, 0, β⟩ : IsingParams ℝ) {i, j} :=
    correlationInfinite_nonneg_of_hβJ (IsingModel.latticeGraph d) Λ
      (mul_nonneg hβ.le (hJ₁.trans hJ₁₂)) {i, j}
  rw [abs_of_nonneg hnn₁]
  calc correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J₁, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J₂, 0, β⟩ : IsingParams ℝ) {i, j} :=
        correlationInfinite_monotone_J (IsingModel.latticeGraph d) Λ (le_refl 0) hβ {i, j}
          (Set.mem_Ici.mpr hJ₁) (Set.mem_Ici.mpr (hJ₁.trans hJ₁₂)) hJ₁₂
      _ ≤ C * Real.exp (-↑α * (IsingModel.latticeDistance d i j : ℝ)) := by
          have hb := hbound i j hij
          rwa [abs_of_nonneg hnn₂] at hb


end Ambient
end IsingModel
