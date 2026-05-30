import IsingModel.Inequalities.HighTemp.Susceptibility

/-!
# Susceptibility infinite-volume ferromagnetic aliases bundle

GJ-proposition-unit bundle of ferromagnetic-form aliases of the
infinite-volume susceptibility bound
`susceptibilityInfinite_latticeGraph_le_of_high_temp` and related variants.

These wrappers take the `Ferromagnetic ⟨J, 0, β⟩` predicate directly,
exposing the simplest API surface for downstream consumers.

**Reference:** Glimm--Jaffe §5.1; Friedli--Velenik §3.7.3.
-/

namespace IsingModel.Ambient

open IsingModel

/-! ## Ferromagnetic-input aliases (cubic exhaustion) -/

/-- **Infinite-volume susceptibility bound from `Ferromagnetic ⟨J, 0, β⟩`**.

Alias of `susceptibilityInfinite_latticeGraph_le_of_high_temp` taking the
`Ferromagnetic` predicate directly. -/
theorem susceptibilityInfinite_latticeGraph_le_of_ferromagnetic_high_temp
    {d : ℕ} {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hlt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ) :
    susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
  susceptibilityInfinite_latticeGraph_le_of_high_temp
    (mul_nonneg hf.hβ.le hf.hJ) hlt i

/-- **Infinite-volume susceptibility bound (general exhaustion)
from `Ferromagnetic ⟨J, 0, β⟩`**. -/
theorem susceptibilityInfinite_latticeGraph_le_of_ferromagnetic_high_temp_gen
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hlt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ) :
    susceptibilityInfinite (latticeGraph d) Λ ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
  susceptibilityInfinite_latticeGraph_le_of_high_temp_gen Λ
    (mul_nonneg hf.hβ.le hf.hJ) hlt i

/-! ## Positivity / nonnegativity of the susceptibility bound -/

/-- **`0 ≤ susceptibility bound` from `0 ≤ β·J·(2d) < 1`**. -/
theorem susceptibility_bound_nonneg
    {β J : ℝ} {d : ℕ}
    (hβJ_nn : 0 ≤ β * J) (hlt : β * J * ↑(2 * d) < 1) :
    0 ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) := by
  have h2d_nn : (0 : ℝ) ≤ 2 * d := by positivity
  have hβJ2d_nn : 0 ≤ β * J * (2 * d) := mul_nonneg hβJ_nn h2d_nn
  have hβJ2d_nn' : 0 ≤ β * J * ↑(2 * d) := by exact_mod_cast hβJ2d_nn
  have h_denom_pos : 0 < 1 - β * J * ↑(2 * d) := by linarith
  exact div_nonneg hβJ2d_nn' h_denom_pos.le

/-- **`susceptibility bound < 1/(1 - β·J·2d)` (general upper)**. -/
theorem susceptibility_bound_lt_one_div
    {β J : ℝ} {d : ℕ}
    (hβJ_nn : 0 ≤ β * J) (hlt : β * J * ↑(2 * d) < 1) :
    β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) <
      1 / (1 - β * J * ↑(2 * d)) := by
  have h2d_nn : (0 : ℝ) ≤ 2 * d := by positivity
  have hβJ2d_nn : 0 ≤ β * J * (2 * d) := mul_nonneg hβJ_nn h2d_nn
  have hβJ2d_lt : β * J * ↑(2 * d) < 1 := hlt
  have h_denom_pos : 0 < 1 - β * J * ↑(2 * d) := by linarith
  rw [div_lt_div_iff_of_pos_right h_denom_pos]
  linarith

/-! ## Squared-form aliases -/

/-- **Squared susceptibility bound: `χ_∞² ≤ (β·J·2d/(1-β·J·2d))²`** under
ferromagnetic + high-temp**.

For nonneg `χ_∞ ≤ M` and `0 ≤ M`, we have `χ_∞² ≤ M²`. The nonnegativity
of `χ_∞` follows from the upper bound being nonneg combined with the
implicit nonneg structure of `susceptibilityInfinite` as a sup of nonneg
quantities. -/
theorem susceptibilityInfinite_squared_le_of_ferromagnetic_high_temp_bound
    {d : ℕ} {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hlt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ)
    (hχ_nn : 0 ≤
      susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i) :
    susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i ^ 2
      ≤ (β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) ^ 2 := by
  have h_le := susceptibilityInfinite_latticeGraph_le_of_ferromagnetic_high_temp hf hlt i
  have h_bd_nn := susceptibility_bound_nonneg (mul_nonneg hf.hβ.le hf.hJ) hlt
  exact sq_le_sq' (by linarith) h_le

/-- **`Ferromagnetic ⟨J, 0, β⟩` ⇒ `0 ≤ β·J`** (helper). -/
theorem ferromagnetic_implies_betaJ_nonneg {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    0 ≤ β * J :=
  mul_nonneg hf.hβ.le hf.hJ

/-- **`Ferromagnetic ⟨J, 0, β⟩` + `β·J·(2d) < 1` ⇒ `0 < 1 - β·J·(2d)`**. -/
theorem one_sub_betaJ_two_d_pos_of_ferromagnetic_high_temp
    {J β : ℝ} {d : ℕ}
    (_hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hlt : β * J * ↑(2 * d) < 1) :
    (0 : ℝ) < 1 - β * J * ↑(2 * d) := by
  linarith

end IsingModel.Ambient
