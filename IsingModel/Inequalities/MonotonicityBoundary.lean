import IsingModel.Inequalities.FKGBoundaryCondition
import Mathlib.Combinatorics.SetFamily.FourFunctions

/-!
# Monotonicity in the boundary condition (Holley's inequality)

For a ferromagnetic Ising model, raising the boundary condition raises the Gibbs
expectation of every monotone observable:

  `η ≤ η'  ⟹  ⟨φ⟩^η_Λ ≤ ⟨φ⟩^{η'}_Λ`   (for nondecreasing `φ`).

This is the cornerstone of the theory of extremal (`+`/`−`) Gibbs states and the
construction of the infinite-volume limit: the maximal (`+`) boundary condition
yields the maximal state, the minimal (`−`) the minimal state, and monotone
observables are squeezed between them.

It is proved via **Holley's inequality**: the two conditioned (boundary-condition)
Boltzmann weights at `η ≤ η'` satisfy the Holley domination condition

  `w^η(a)·w^{η'}(b) ≤ w^η(a ⊓ b)·w^{η'}(a ⊔ b)`.

The key point is the interaction of the conditioning with the order: if `a` agrees
with `η` off `Λ` and `b` agrees with `η'` off `Λ`, then (since `η ≤ η'`) `a ⊓ b`
agrees with `η` off `Λ` (`η ⊓ η' = η`) and `a ⊔ b` agrees with `η'` off `Λ`
(`η ⊔ η' = η'`), so all four weights are the inhomogeneous weight and the
condition reduces to `boltzmannWeightJ_log_supermodular`; if either disagrees, the
left side vanishes.

* `agreesOff_inf_of_le` / `agreesOff_sup_of_le` — the order-aware conditioning
  closure.
* `boltzmannWeightBC_cross_supermodular` — the Holley domination condition.
* `gibbsExpectationBC_boundary_mono_of_nonneg` / `gibbsExpectationBC_boundary_mono`
  — boundary-condition monotonicity for nonnegative / arbitrary monotone
  observables.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
§3.6.2 and §6 (boundary conditions and extremal states).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Order-aware conditioning closure -/

omit [Fintype ι] [DecidableEq ι] in
/-- **Lower closure under `⊓` for `η ≤ η'`**: if `a` agrees with `η` off `Λ` and
`b` agrees with `η'` off `Λ`, then `a ⊓ b` agrees with `η` off `Λ` (off `Λ`,
`a ⊓ b = η ⊓ η' = η` since `η ≤ η'`). -/
theorem agreesOff_inf_of_le {Λ : Finset ι} {η η' a b : Config ι} (hη : η ≤ η')
    (ha : agreesOff Λ η a) (hb : agreesOff Λ η' b) : agreesOff Λ η (a ⊓ b) := by
  intro i hi
  rw [Pi.inf_apply, ha i hi, hb i hi, inf_eq_left.mpr (hη i)]

omit [Fintype ι] [DecidableEq ι] in
/-- **Upper closure under `⊔` for `η ≤ η'`**: if `a` agrees with `η` off `Λ` and
`b` agrees with `η'` off `Λ`, then `a ⊔ b` agrees with `η'` off `Λ` (off `Λ`,
`a ⊔ b = η ⊔ η' = η'` since `η ≤ η'`). -/
theorem agreesOff_sup_of_le {Λ : Finset ι} {η η' a b : Config ι} (hη : η ≤ η')
    (ha : agreesOff Λ η a) (hb : agreesOff Λ η' b) : agreesOff Λ η' (a ⊔ b) := by
  intro i hi
  rw [Pi.sup_apply, ha i hi, hb i hi, sup_eq_right.mpr (hη i)]

/-! ## Holley domination condition for ordered boundary conditions -/

omit [DecidableEq ι] in
/-- **Holley domination condition for ordered boundary conditions**: for `β ≥ 0`,
`J(e) ≥ 0`, and `η ≤ η'`,

`w^η(a)·w^{η'}(b) ≤ w^η(a ⊓ b)·w^{η'}(a ⊔ b)`.

If both `a` agrees with `η` and `b` agrees with `η'` off `Λ`, the conditioning
closure (`agreesOff_inf_of_le` / `agreesOff_sup_of_le`) keeps all four weights
equal to the inhomogeneous weight, so the condition is
`boltzmannWeightJ_log_supermodular`.  Otherwise the left side vanishes. -/
theorem boltzmannWeightBC_cross_supermodular (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} {J : Sym2 ι → ℝ} {h : ℝ} (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (Λ : Finset ι) {η η' : Config ι} (hη : η ≤ η') (a b : Config ι) :
    boltzmannWeightBC G β J h Λ η a * boltzmannWeightBC G β J h Λ η' b ≤
      boltzmannWeightBC G β J h Λ η (a ⊓ b) * boltzmannWeightBC G β J h Λ η' (a ⊔ b) := by
  by_cases ha : agreesOff Λ η a
  · by_cases hb : agreesOff Λ η' b
    · rw [boltzmannWeightBC_of_agrees G β J h ha, boltzmannWeightBC_of_agrees G β J h hb,
        boltzmannWeightBC_of_agrees G β J h (agreesOff_inf_of_le hη ha hb),
        boltzmannWeightBC_of_agrees G β J h (agreesOff_sup_of_le hη ha hb)]
      have hlsm := boltzmannWeightJ_log_supermodular (h := h) G hβ hJ a b
      linarith [mul_comm (boltzmannWeightJ G β J h (a ⊔ b)) (boltzmannWeightJ G β J h (a ⊓ b))]
    · rw [boltzmannWeightBC_of_not_agrees G β J h hb, mul_zero]
      exact mul_nonneg (boltzmannWeightBC_nonneg G β J h Λ η _)
        (boltzmannWeightBC_nonneg G β J h Λ η' _)
  · rw [boltzmannWeightBC_of_not_agrees G β J h ha, zero_mul]
    exact mul_nonneg (boltzmannWeightBC_nonneg G β J h Λ η _)
      (boltzmannWeightBC_nonneg G β J h Λ η' _)

/-! ## Monotonicity in the boundary condition -/

/-- **Boundary-condition monotonicity, nonnegative case**: for `β ≥ 0`,
`J(e) ≥ 0`, `η ≤ η'`, and a nonnegative monotone nondecreasing observable `φ`,
`⟨φ⟩^η_Λ ≤ ⟨φ⟩^{η'}_Λ`.

Apply Holley's inequality to the two normalised boundary-condition Boltzmann
weights, whose domination condition is `boltzmannWeightBC_cross_supermodular`. -/
theorem gibbsExpectationBC_boundary_mono_of_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} {J : Sym2 ι → ℝ} {h : ℝ} (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (Λ : Finset ι) {η η' : Config ι} (hη : η ≤ η')
    (φ : Config ι → ℝ) (hφ_nn : 0 ≤ φ) (hφ_mono : Monotone φ) :
    gibbsExpectationBC G β J h Λ η φ ≤ gibbsExpectationBC G β J h Λ η' φ := by
  classical
  set Zη := partitionFunctionBC G β J h Λ η with hZη_def
  set Zη' := partitionFunctionBC G β J h Λ η' with hZη'_def
  have hZη : 0 < Zη := partitionFunctionBC_pos G β J h Λ η
  have hZη' : 0 < Zη' := partitionFunctionBC_pos G β J h Λ η'
  set fm : Config ι → ℝ := fun σ => boltzmannWeightBC G β J h Λ η σ / Zη with hfm_def
  set gm : Config ι → ℝ := fun σ => boltzmannWeightBC G β J h Λ η' σ / Zη' with hgm_def
  have hfm_nn : 0 ≤ fm := fun σ => div_nonneg (boltzmannWeightBC_nonneg G β J h Λ η σ) hZη.le
  have hgm_nn : 0 ≤ gm := fun σ => div_nonneg (boltzmannWeightBC_nonneg G β J h Λ η' σ) hZη'.le
  have hsum_fm : ∑ σ : Config ι, fm σ = 1 := by
    simp only [hfm_def, div_eq_mul_inv, ← Finset.sum_mul]
    rw [show (∑ σ : Config ι, boltzmannWeightBC G β J h Λ η σ) = Zη from rfl,
      mul_inv_cancel₀ (ne_of_gt hZη)]
  have hsum_gm : ∑ σ : Config ι, gm σ = 1 := by
    simp only [hgm_def, div_eq_mul_inv, ← Finset.sum_mul]
    rw [show (∑ σ : Config ι, boltzmannWeightBC G β J h Λ η' σ) = Zη' from rfl,
      mul_inv_cancel₀ (ne_of_gt hZη')]
  have hfg : ∑ σ : Config ι, fm σ = ∑ σ : Config ι, gm σ := by rw [hsum_fm, hsum_gm]
  have hcross : ∀ a b : Config ι, fm a * gm b ≤ fm (a ⊓ b) * gm (a ⊔ b) := by
    intro a b
    simp only [hfm_def, hgm_def, div_mul_div_comm]
    exact (div_le_div_iff_of_pos_right (mul_pos hZη hZη')).mpr
      (boltzmannWeightBC_cross_supermodular G hβ hJ Λ hη a b)
  have hhol := holley (μ := φ) (f := fm) (g := gm) hφ_nn hfm_nn hgm_nn hφ_mono hfg hcross
  have hEη : gibbsExpectationBC G β J h Λ η φ = ∑ σ : Config ι, φ σ * fm σ := by
    unfold gibbsExpectationBC
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [hfm_def, hZη_def]
    rw [div_eq_inv_mul]
    ring
  have hEη' : gibbsExpectationBC G β J h Λ η' φ = ∑ σ : Config ι, φ σ * gm σ := by
    unfold gibbsExpectationBC
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [hgm_def, hZη'_def]
    rw [div_eq_inv_mul]
    ring
  rw [hEη, hEη']
  exact hhol

/-- **Boundary-condition monotonicity** (Holley): for `β ≥ 0`, `J(e) ≥ 0`,
`η ≤ η'`, and **any** monotone nondecreasing observable `φ` (of arbitrary sign),
`⟨φ⟩^η_Λ ≤ ⟨φ⟩^{η'}_Λ`.

Drops the nonnegativity hypothesis by the constant shift (the inequality is
invariant under `φ ↦ φ − c`, since `⟨1⟩ = 1`). -/
theorem gibbsExpectationBC_boundary_mono (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} {J : Sym2 ι → ℝ} {h : ℝ} (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (Λ : Finset ι) {η η' : Config ι} (hη : η ≤ η')
    (φ : Config ι → ℝ) (hφ_mono : Monotone φ) :
    gibbsExpectationBC G β J h Λ η φ ≤ gibbsExpectationBC G β J h Λ η' φ := by
  classical
  have huniv : (Finset.univ : Finset (Config ι)).Nonempty := Finset.univ_nonempty
  set c : ℝ := Finset.univ.inf' huniv φ with hc_def
  have hc : ∀ σ : Config ι, c ≤ φ σ := fun σ => Finset.inf'_le φ (Finset.mem_univ σ)
  set φ' : Config ι → ℝ := fun σ => φ σ - c with hφ'_def
  have hφ'_nn : 0 ≤ φ' := fun σ => sub_nonneg.mpr (hc σ)
  have hφ'_mono : Monotone φ' := fun x y hxy => sub_le_sub_right (hφ_mono hxy) c
  have hEη : gibbsExpectationBC G β J h Λ η φ' = gibbsExpectationBC G β J h Λ η φ - c := by
    have hrw : φ' = φ + (fun _ => -c) := by funext σ; simp [hφ'_def, Pi.add_apply]; ring
    rw [hrw, gibbsExpectationBC_add, gibbsExpectationBC_const]; ring
  have hEη' : gibbsExpectationBC G β J h Λ η' φ' = gibbsExpectationBC G β J h Λ η' φ - c := by
    have hrw : φ' = φ + (fun _ => -c) := by funext σ; simp [hφ'_def, Pi.add_apply]; ring
    rw [hrw, gibbsExpectationBC_add, gibbsExpectationBC_const]; ring
  have hmono := gibbsExpectationBC_boundary_mono_of_nonneg (h := h) G hβ hJ Λ hη φ' hφ'_nn hφ'_mono
  rw [hEη, hEη'] at hmono
  linarith [hmono]

end IsingModel
