import IsingModel.PseudoMass.FromParamsBasic.JZeroEquiv

/-!
# Pseudo-mass from parameters: monotonicity and bounds

Monotonicity in trivial slices and correlation-bound comparisons.
-/

namespace IsingModel

open Set Real Filter

/-- **At `J = 0` for distinct pair, `pseudoMassFromParamsAtPair` depends
only on the product `β·h`**: for any two ferromagnetic params
`⟨0, h₁, β₁⟩` and `⟨0, h₂, β₂⟩` with `β₁·h₁ = β₂·h₂`, the bridge values
agree. Direct corollary of `pseudoMassFromParamsAtPair_at_J_zero_distinct_eq`
which gives `pseudoMassExt(tanh(β·h)^2)` — only the product enters
the right-hand side. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_eq_of_product_eq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h₁ β₁ h₂ β₂ : ℝ}
    (hf₁ : Ferromagnetic (⟨(0 : ℝ), h₁, β₁⟩ : IsingParams ℝ))
    (hf₂ : Ferromagnetic (⟨(0 : ℝ), h₂, β₂⟩ : IsingParams ℝ))
    (hprod : β₁ * h₁ = β₂ * h₂)
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h₁, β₁⟩ : IsingParams ℝ) x z =
      pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h₂, β₂⟩ : IsingParams ℝ) x z := by
  rw [pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf₁ hxz,
      pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf₂ hxz,
      hprod]

/-- **`pseudoMassFromParamsAtPair` strictly anti in `h` at `J = 0`** for
distinct pair, β > 0, h > 0: `tanh(β·h)^2` increases (in `Ioo 0 1 ⊂ Ioo 0 2`)
as h increases (β > 0 fixed), and `pseudoMassExt` is strictly antitone
on `Ioo 0 2`. Companion to `_strictAntiOn_beta_at_J_zero` (β-direction
analogue, PR #1668). -/
theorem pseudoMassFromParamsAtPair_strictAntiOn_h_at_J_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    StrictAntiOn (fun h =>
        pseudoMassFromParamsAtPair hα hr d Λ
          (⟨0, h, β⟩ : IsingParams ℝ) x z) (Set.Ioi 0) := by
  intro h₁ hh₁ h₂ hh₂ hlt
  simp only [Set.mem_Ioi] at hh₁ hh₂
  have hf₁ : Ferromagnetic (⟨(0 : ℝ), h₁, β⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, hh₁.le, hβ⟩
  have hf₂ : Ferromagnetic (⟨(0 : ℝ), h₂, β⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, hh₂.le, hβ⟩
  change pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h₂, β⟩ : IsingParams ℝ) x z
        < pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h₁, β⟩ : IsingParams ℝ) x z
  rw [pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf₁ hxz,
      pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf₂ hxz]
  have htanh_pos₁ : 0 < Real.tanh (β * h₁) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ hh₁)) (Real.cosh_pos _)
  have htanh_pos₂ : 0 < Real.tanh (β * h₂) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ hh₂)) (Real.cosh_pos _)
  have htanh_mono : Real.tanh (β * h₁) < Real.tanh (β * h₂) :=
    Real.tanh_strictMono (mul_lt_mul_of_pos_left hlt hβ)
  have hsq_lt : Real.tanh (β * h₁) ^ 2 < Real.tanh (β * h₂) ^ 2 := by
    have h1 : Real.tanh (β * h₁) ^ 2 = Real.tanh (β * h₁) * Real.tanh (β * h₁) := sq _
    have h2 : Real.tanh (β * h₂) ^ 2 = Real.tanh (β * h₂) * Real.tanh (β * h₂) := sq _
    rw [h1, h2]
    exact mul_lt_mul' htanh_mono.le htanh_mono htanh_pos₁.le htanh_pos₂
  have hmem₁ : Real.tanh (β * h₁) ^ 2 ∈ Set.Ioo (0 : ℝ) 2 := by
    refine ⟨by positivity, ?_⟩
    have habs : |Real.tanh (β * h₁)| < 1 := Real.abs_tanh_lt_one _
    have h1 : -1 < Real.tanh (β * h₁) := neg_lt_of_abs_lt habs
    have h2 : Real.tanh (β * h₁) < 1 := lt_of_abs_lt habs
    nlinarith
  have hmem₂ : Real.tanh (β * h₂) ^ 2 ∈ Set.Ioo (0 : ℝ) 2 := by
    refine ⟨by positivity, ?_⟩
    have habs : |Real.tanh (β * h₂)| < 1 := Real.abs_tanh_lt_one _
    have h1 : -1 < Real.tanh (β * h₂) := neg_lt_of_abs_lt habs
    have h2 : Real.tanh (β * h₂) < 1 := lt_of_abs_lt habs
    nlinarith
  exact pseudoMassExt_strictAntiOn hα hr hmem₁ hmem₂ hsq_lt

/-- **`pseudoMassFromParamsAtPair` at `J = 0, h = 0` distinct pair = 0**:
combining `pseudoMassFromParamsAtPair_at_h_zero_eq` with
`Ambient.truncated2Infinite_J_zero_of_ne` (which gives 0 for distinct
pair under ferromagnetic, J = 0). Direct corollary at the `J = h = 0`
trivial slice. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_h_zero_eq_zero {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, 0, β⟩ : IsingParams ℝ) x z = 0 := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq hα hr d Λ 0 β x z]
  have hf : Ferromagnetic (⟨(0 : ℝ), 0, β⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, le_refl 0, hβ⟩
  rw [Ambient.truncated2Infinite_J_zero_of_ne (IsingModel.latticeGraph d) Λ 0 β hf hxz]
  apply pseudoMassExt_of_not_mem
  intro hmem
  exact lt_irrefl 0 hmem.1

/-- **`pseudoMassFromParamsAtPair > 0 at `h = 0` ↔ `0 < truncated2Infinite`**:
under ferromagnetic params, since `truncated2Infinite ∈ [0, 1] ⊂ [0, 2)`
(`truncated2Infinite_nonneg` + `truncated2Infinite_le_one`), the
`Ioo 0 2` membership of truncated2 is equivalent to strict positivity.
Combined with `pseudoMassFromParamsAtPair_at_h_zero_eq` and
`pseudoMassExt_pos_iff` to give the iff in terms of truncated2. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_pos_iff {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (x z : Fin d → ℤ) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ↔
    0 < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq hα hr d Λ J β x z]
  rw [pseudoMassExt_pos_iff hα hr]
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have hnonneg : 0 ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                        (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
    Ambient.truncated2Infinite_nonneg (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hf x z
  have hle : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ 1 :=
    Ambient.truncated2Infinite_le_one (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hf x z
  refine ⟨fun h => h.1, fun h => ⟨h, by linarith⟩⟩

/-- **`pseudoMassFromParamsAtPair = 0 at `h = 0` ↔ `truncated2Infinite = 0`**:
contrapositive form of `_at_h_zero_pos_iff` under non-negativity of
truncated2 (which holds in the ferromagnetic regime). -/
theorem pseudoMassFromParamsAtPair_at_h_zero_eq_zero_iff {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z = 0 ↔
    Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z = 0 := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have hnonneg : 0 ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                        (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
    Ambient.truncated2Infinite_nonneg (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hf x z
  have hpm_nonneg : 0 ≤ pseudoMassFromParamsAtPair hα hr d Λ
                          (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
    pseudoMassFromParamsAtPair_nonneg hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z
  constructor
  · intro hzero
    by_contra h_t_ne
    have h_t_pos : 0 < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                          (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
      lt_of_le_of_ne hnonneg (Ne.symm h_t_ne)
    have hpos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
      (pseudoMassFromParamsAtPair_at_h_zero_pos_iff hα hr d Λ hJ hβ x z).mpr h_t_pos
    linarith
  · intro hzero
    by_contra h_pm_ne
    have h_pm_pos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
                          (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
      lt_of_le_of_ne hpm_nonneg (Ne.symm h_pm_ne)
    have h_t_pos : 0 < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                          (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
      (pseudoMassFromParamsAtPair_at_h_zero_pos_iff hα hr d Λ hJ hβ x z).mp h_pm_pos
    linarith

/-- **`pseudoMassFromParamsAtPair` upper-bounded by `pseudoMass` at a
positive correlation lower bound**: if `c_min ≤ correlationInfinite ...`
with `c_min ∈ Ioo 0 2`, then by anti-monotonicity, `pseudoMassFromParamsAtPair
≤ pseudoMass(c_min)`. (Requires correlation also in `Ioo 0 2`.) -/
theorem pseudoMassFromParamsAtPair_le_of_corr_ge {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c_min : ℝ} (hc_min : c_min ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2)
    (hge : c_min ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z ≤ pseudoMassExt hα hr c_min := by
  unfold pseudoMassFromParamsAtPair
  by_cases heq :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} = c_min
  · rw [heq]
  · have hlt : c_min <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} :=
      lt_of_le_of_ne hge (Ne.symm heq)
    exact le_of_lt
      (pseudoMassExt_strictAntiOn hα hr hc_min hcorr hlt)

/-- **`pseudoMassFromParamsAtPair` lower-bounded by `pseudoMass` at a
correlation upper bound**: if `correlationInfinite ... ≤ c_max` with
`c_max ∈ Ioo 0 2`, then by anti-monotonicity, `pseudoMassExt c_max ≤
pseudoMassFromParamsAtPair`. -/
theorem pseudoMassFromParamsAtPair_ge_of_corr_le {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c_max : ℝ} (hc_max : c_max ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2)
    (hle : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ≤ c_max) :
    pseudoMassExt hα hr c_max ≤ pseudoMassFromParamsAtPair hα hr d Λ p x z := by
  unfold pseudoMassFromParamsAtPair
  by_cases heq :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} = c_max
  · rw [heq]
  · have hlt :
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} <
          c_max := lt_of_le_of_ne hle heq
    exact le_of_lt
      (pseudoMassExt_strictAntiOn hα hr hcorr hc_max hlt)

/-- **`pseudoMassFromParamsAtPair` strictly anti in β at `J = 0`** for
distinct pair, `h > 0`, β > 0: as β increases, `tanh(βh)^2` increases
(remaining in `Ioo 0 1 ⊂ Ioo 0 2`), and `pseudoMass` is strictly
antitone in its correlation argument. -/
theorem pseudoMassFromParamsAtPair_strictAntiOn_beta_at_J_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 < h) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    StrictAntiOn (fun β =>
        pseudoMassFromParamsAtPair hα hr d Λ
          (⟨0, h, β⟩ : IsingParams ℝ) x z) (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ hβ₂ hlt
  simp only [Set.mem_Ioi] at hβ₁ hβ₂
  have hf₁ : Ferromagnetic (⟨(0 : ℝ), h, β₁⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, hh.le, hβ₁⟩
  have hf₂ : Ferromagnetic (⟨(0 : ℝ), h, β₂⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, hh.le, hβ₂⟩
  change pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β₂⟩ : IsingParams ℝ) x z
        < pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β₁⟩ : IsingParams ℝ) x z
  rw [pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf₁ hxz,
      pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf₂ hxz]
  have htanh_pos₁ : 0 < Real.tanh (β₁ * h) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ₁ hh)) (Real.cosh_pos _)
  have htanh_pos₂ : 0 < Real.tanh (β₂ * h) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ₂ hh)) (Real.cosh_pos _)
  have htanh_mono : Real.tanh (β₁ * h) < Real.tanh (β₂ * h) :=
    Real.tanh_strictMono (mul_lt_mul_of_pos_right hlt hh)
  have hsq_lt : Real.tanh (β₁ * h) ^ 2 < Real.tanh (β₂ * h) ^ 2 := by
    have h1 : Real.tanh (β₁ * h) ^ 2 = Real.tanh (β₁ * h) * Real.tanh (β₁ * h) := sq _
    have h2 : Real.tanh (β₂ * h) ^ 2 = Real.tanh (β₂ * h) * Real.tanh (β₂ * h) := sq _
    rw [h1, h2]
    exact mul_lt_mul' htanh_mono.le htanh_mono htanh_pos₁.le htanh_pos₂
  have hmem₁ : Real.tanh (β₁ * h) ^ 2 ∈ Set.Ioo (0 : ℝ) 2 := by
    refine ⟨by positivity, ?_⟩
    have habs : |Real.tanh (β₁ * h)| < 1 := Real.abs_tanh_lt_one _
    have h1 : -1 < Real.tanh (β₁ * h) := neg_lt_of_abs_lt habs
    have h2 : Real.tanh (β₁ * h) < 1 := lt_of_abs_lt habs
    nlinarith
  have hmem₂ : Real.tanh (β₂ * h) ^ 2 ∈ Set.Ioo (0 : ℝ) 2 := by
    refine ⟨by positivity, ?_⟩
    have habs : |Real.tanh (β₂ * h)| < 1 := Real.abs_tanh_lt_one _
    have h1 : -1 < Real.tanh (β₂ * h) := neg_lt_of_abs_lt habs
    have h2 : Real.tanh (β₂ * h) < 1 := lt_of_abs_lt habs
    nlinarith
  exact pseudoMassExt_strictAntiOn hα hr hmem₁ hmem₂ hsq_lt

end IsingModel
