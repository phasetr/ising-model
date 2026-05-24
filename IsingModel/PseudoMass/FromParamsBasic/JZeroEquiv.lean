import IsingModel.PseudoMass.FromParamsBasic.BasicSlices

/-!
# Pseudo-mass from parameters: J = 0 equivalences

Explicit J-zero and h-zero bridge identities for the concrete pseudo-mass wrapper.
-/

namespace IsingModel

open Set Real Filter

/-- **`pseudoMassFromParamsAtPair` is positive at `J = 0, h > 0, β > 0`
for distinct sites**: the correlation equals `tanh(β·h)^2 ∈ (0, 1) ⊂ Ioo 0 2`,
hence `pseudoMassFromParamsAtPair > 0`. -/
theorem pseudoMassFromParamsAtPair_pos_at_J_zero {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z := by
  apply pseudoMassFromParamsAtPair_pos_of_corr_mem
  -- correlation = tanh(β·h)^|{x, z}| = tanh(β·h)^2
  have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) := ⟨le_refl 0, hh.le, hβ⟩
  have hcorr := Ambient.correlationInfinite_J_zero
    (IsingModel.latticeGraph d) Λ h β hf {x, z}
  rw [hcorr]
  -- |{x, z}| = 2 since x ≠ z
  have hcard : ({x, z} : Finset (Fin d → ℤ)).card = 2 := by
    rw [Finset.card_pair hxz]
  rw [hcard]
  refine ⟨?_, ?_⟩
  · -- 0 < tanh(βh)^2
    have htanh_pos : 0 < Real.tanh (β * h) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ hh)) (Real.cosh_pos _)
    positivity
  · -- tanh(βh)^2 < 2: tanh ∈ (-1, 1) so tanh^2 < 1 < 2
    have htanh_abs : |Real.tanh (β * h)| < 1 := Real.abs_tanh_lt_one _
    have hsq_lt : Real.tanh (β * h) ^ 2 < 1 := by
      have h1 : -1 < Real.tanh (β * h) := neg_lt_of_abs_lt htanh_abs
      have h2 : Real.tanh (β * h) < 1 := lt_of_abs_lt htanh_abs
      nlinarith
    linarith

/-- **`pseudoMassFromParamsAtPair` at `J = 0` explicit form**: equals
`pseudoMass` evaluated at `tanh(βh)^|{x,z}|`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_eq {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z =
      pseudoMassExt hα hr (Real.tanh (β * h) ^
                            ({x, z} : Finset (Fin d → ℤ)).card) := by
  unfold pseudoMassFromParamsAtPair
  rw [Ambient.correlationInfinite_J_zero (IsingModel.latticeGraph d) Λ h β hf {x, z}]

/-- **`pseudoMassFromParamsAtPair_at_J_zero_eq` distinct form**:
under `x ≠ z`, the cardinality is 2, giving an explicit `tanh^2`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_eq {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z =
      pseudoMassExt hα hr (Real.tanh (β * h) ^ 2) := by
  rw [pseudoMassFromParamsAtPair_at_J_zero_eq hα hr d Λ hf x z, Finset.card_pair hxz]

/-- **`pseudoMassFromParamsAtPair` at `h = 0` equals
`pseudoMassExt(truncated2Infinite)`**: at zero external field, the
unconnected pair correlation `⟨σ_x σ_z⟩` agrees with the truncated
2-point Ursell function `⟨σ_x σ_z⟩ - ⟨σ_x⟩⟨σ_z⟩`, since the spin-flip
symmetry forces `⟨σ_x⟩ = ⟨σ_z⟩ = 0`. Thus

  `pseudoMassFromParamsAtPair hα hr d Λ ⟨J, 0, β⟩ x z =
   pseudoMassExt hα hr (truncated2Infinite (latticeGraph d) Λ ⟨J,0,β⟩ x z)`.

This is the bridge identity needed to compare `pseudoMassFromParamsAtPair`
to `latticeMass`, which is defined as the supremum of validating
exponential decay rates of `truncated2Infinite`. (Step 117l support,
Issue #1645.) -/
theorem pseudoMassFromParamsAtPair_at_h_zero_eq {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z =
      pseudoMassExt hα hr
        (Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  unfold pseudoMassFromParamsAtPair
  rw [Ambient.truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β x z]

/-- **At `J = 0` distinct pair, ferromagnetic, `0 < pseudoMassFromParamsAtPair`
iff `0 < h`**: under `Ferromagnetic ⟨0, h, β⟩` (which gives `0 ≤ h`, `0 < β`)
and `x ≠ z`, `0 < pseudoMassFromParamsAtPair ↔ 0 < h`. The forward
direction follows from `_at_J_zero_distinct_eq` + `pseudoMassExt_pos_iff`
(forces `tanh(β·h)^2 ∈ Ioo 0 2`, hence `tanh(β·h) ≠ 0`, hence `β·h ≠ 0`,
combined with `β > 0` gives `h ≠ 0`, then `h > 0` from `h ≥ 0`).
The reverse is `pseudoMassFromParamsAtPair_pos_at_J_zero` (already
proven). -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_pos_iff_h_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ
          (⟨0, h, β⟩ : IsingParams ℝ) x z ↔ 0 < h := by
  refine ⟨?_, fun hh => pseudoMassFromParamsAtPair_pos_at_J_zero hα hr d Λ hh hf.hβ hxz⟩
  intro hpos
  rw [pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf hxz] at hpos
  rw [pseudoMassExt_pos_iff hα hr] at hpos
  have htanh_sq_pos : 0 < Real.tanh (β * h) ^ 2 := hpos.1
  have htanh_ne : Real.tanh (β * h) ≠ 0 := by
    intro habs
    rw [habs] at htanh_sq_pos
    norm_num at htanh_sq_pos
  have hβh_ne : β * h ≠ 0 := by
    intro habs
    rw [habs, Real.tanh_zero] at htanh_ne
    exact htanh_ne rfl
  have hh_ne : h ≠ 0 := by
    intro h_eq
    rw [h_eq, mul_zero] at hβh_ne
    exact hβh_ne rfl
  exact lt_of_le_of_ne hf.hh (Ne.symm hh_ne)

/-- **At `J = 0` distinct pair, ferromagnetic, `pseudoMassFromParamsAtPair = 0`
iff `h = 0`**: contrapositive of `_at_J_zero_distinct_pos_iff_h_pos`,
using non-negativity to flip the strict iff. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_zero_iff_h_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ
        (⟨0, h, β⟩ : IsingParams ℝ) x z = 0 ↔ h = 0 := by
  have hh_nonneg : 0 ≤ h := hf.hh
  have hpm_nonneg := pseudoMassFromParamsAtPair_nonneg hα hr d Λ
                        (⟨0, h, β⟩ : IsingParams ℝ) x z
  constructor
  · intro h_eq
    by_contra h_ne
    have hh_pos : 0 < h := lt_of_le_of_ne hh_nonneg (Ne.symm h_ne)
    have hpm_pos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
                          (⟨0, h, β⟩ : IsingParams ℝ) x z :=
      (pseudoMassFromParamsAtPair_at_J_zero_distinct_pos_iff_h_pos
        hα hr d Λ hf hxz).mpr hh_pos
    linarith
  · intro hh_eq
    by_contra h_pm_ne
    have hpm_pos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
                          (⟨0, h, β⟩ : IsingParams ℝ) x z :=
      lt_of_le_of_ne hpm_nonneg (Ne.symm h_pm_ne)
    have hh_pos : 0 < h :=
      (pseudoMassFromParamsAtPair_at_J_zero_distinct_pos_iff_h_pos
        hα hr d Λ hf hxz).mp hpm_pos
    linarith

end IsingModel
