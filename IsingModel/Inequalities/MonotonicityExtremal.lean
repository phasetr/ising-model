import IsingModel.Inequalities.MonotonicityBoundary

/-!
# Extremal boundary states and magnetization ordering (FV §6)

The boundary-condition monotonicity `gibbsExpectationBC_boundary_mono` has its
sharpest form at the two extremal boundary conditions:

* the **`+` boundary** `plusConfig` (all spins up), the maximal configuration;
* the **`−` boundary** `minusConfig` (all spins down), the minimal configuration.

For every boundary condition `η` and every monotone observable `φ`,

  `⟨φ⟩^{−}_Λ ≤ ⟨φ⟩^{η}_Λ ≤ ⟨φ⟩^{+}_Λ`,

so the `±` boundary conditions bracket all boundary conditions: at this finite
volume the `+` boundary condition gives the largest expectation of every monotone
observable, and the `−` the smallest.  This finite-volume bracketing is the
foundation for the extremal infinite-volume `±` Gibbs states (constructed as the
thermodynamic limits of these boundary conditions).

As a concrete application, the single-spin observable `σ ↦ s(σ_i)` is monotone, so
the **local magnetization is squeezed by the extremal states**:

  `⟨σ_i⟩^{−}_Λ ≤ ⟨σ_i⟩^{η}_Λ ≤ ⟨σ_i⟩^{+}_Λ`.

* `plusConfig` / `minusConfig` + `le_plusConfig` / `minusConfig_le` — the extremal
  configurations.
* `gibbsExpectationBC_le_plus` / `gibbsExpectationBC_minus_le` /
  `gibbsExpectationBC_extremal_sandwich` — the bracketing of monotone observables.
* `spin_sign_monotone` / `singleSpinObs_monotone` and
  `magnetizationBC_extremal_sandwich` — the magnetization ordering.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
§6 (the extremal `±` states).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Extremal configurations -/

/-- The **`+` configuration** (all spins up), the maximal element of `Config ι`. -/
def plusConfig (ι : Type*) : Config ι := fun _ => Spin.up

/-- The **`−` configuration** (all spins down), the minimal element of `Config ι`. -/
def minusConfig (ι : Type*) : Config ι := fun _ => Spin.down

omit [Fintype ι] [DecidableEq ι] in
/-- Every spin is `≤ up`. -/
theorem Spin.le_up (s : Spin) : s ≤ Spin.up := by cases s <;> decide

omit [Fintype ι] [DecidableEq ι] in
/-- Every spin is `≥ down`. -/
theorem Spin.down_le (s : Spin) : Spin.down ≤ s := by cases s <;> decide

omit [Fintype ι] [DecidableEq ι] in
/-- The `+` configuration is the maximum: `σ ≤ plusConfig`. -/
theorem le_plusConfig (σ : Config ι) : σ ≤ plusConfig ι := fun i => Spin.le_up (σ i)

omit [Fintype ι] [DecidableEq ι] in
/-- The `−` configuration is the minimum: `minusConfig ≤ σ`. -/
theorem minusConfig_le (σ : Config ι) : minusConfig ι ≤ σ := fun i => Spin.down_le (σ i)

/-! ## Extremal bracketing of monotone observables -/

/-- **Upper extremal bound**: for any boundary condition `η`, `⟨φ⟩^η_Λ ≤ ⟨φ⟩^+_Λ`
(the `+` state dominates every boundary condition for monotone `φ`). -/
theorem gibbsExpectationBC_le_plus (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} {J : Sym2 ι → ℝ} {h : ℝ} (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (Λ : Finset ι) (η : Config ι)
    (φ : Config ι → ℝ) (hφ_mono : Monotone φ) :
    gibbsExpectationBC G β J h Λ η φ ≤ gibbsExpectationBC G β J h Λ (plusConfig ι) φ :=
  gibbsExpectationBC_boundary_mono G hβ hJ Λ (le_plusConfig η) φ hφ_mono

/-- **Lower extremal bound**: for any boundary condition `η`, `⟨φ⟩^−_Λ ≤ ⟨φ⟩^η_Λ`
(the `−` state is dominated by every boundary condition for monotone `φ`). -/
theorem gibbsExpectationBC_minus_le (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} {J : Sym2 ι → ℝ} {h : ℝ} (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (Λ : Finset ι) (η : Config ι)
    (φ : Config ι → ℝ) (hφ_mono : Monotone φ) :
    gibbsExpectationBC G β J h Λ (minusConfig ι) φ ≤ gibbsExpectationBC G β J h Λ η φ :=
  gibbsExpectationBC_boundary_mono G hβ hJ Λ (minusConfig_le η) φ hφ_mono

/-- **Extremal sandwich**: every boundary-condition expectation of a monotone
observable lies between the `−` and `+` states:
`⟨φ⟩^−_Λ ≤ ⟨φ⟩^η_Λ ≤ ⟨φ⟩^+_Λ`. -/
theorem gibbsExpectationBC_extremal_sandwich (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} {J : Sym2 ι → ℝ} {h : ℝ} (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (Λ : Finset ι) (η : Config ι)
    (φ : Config ι → ℝ) (hφ_mono : Monotone φ) :
    gibbsExpectationBC G β J h Λ (minusConfig ι) φ ≤ gibbsExpectationBC G β J h Λ η φ ∧
      gibbsExpectationBC G β J h Λ η φ ≤ gibbsExpectationBC G β J h Λ (plusConfig ι) φ :=
  ⟨gibbsExpectationBC_minus_le G hβ hJ Λ η φ hφ_mono,
    gibbsExpectationBC_le_plus G hβ hJ Λ η φ hφ_mono⟩

/-! ## Magnetization ordering -/

omit [Fintype ι] [DecidableEq ι] in
/-- The spin sign `Spin.sign ℝ` is monotone (`down ↦ −1 ≤ +1 ↦ up`). -/
theorem spin_sign_monotone : Monotone (Spin.sign ℝ) := by
  intro a b hab
  cases a <;> cases b
  · norm_num [Spin.sign, Spin.toSign]
  · exact absurd (le_antisymm hab (Spin.down_le Spin.up)) (by decide)
  · norm_num [Spin.sign, Spin.toSign]
  · norm_num [Spin.sign, Spin.toSign]

omit [Fintype ι] [DecidableEq ι] in
/-- The **single-spin observable** `σ ↦ s(σ_i)` is monotone in the configuration
order. -/
theorem singleSpinObs_monotone (i : ι) :
    Monotone (fun σ : Config ι => Spin.sign ℝ (σ i)) :=
  fun _ _ hσ => spin_sign_monotone (hσ i)

/-- **Extremal sandwich for the local magnetization**: the expected single spin at
site `i` under any boundary condition lies between the `−` and `+` states,
`⟨s(σ_i)⟩^−_Λ ≤ ⟨s(σ_i)⟩^η_Λ ≤ ⟨s(σ_i)⟩^+_Λ`. -/
theorem magnetizationBC_extremal_sandwich (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} {J : Sym2 ι → ℝ} {h : ℝ} (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (Λ : Finset ι) (η : Config ι) (i : ι) :
    gibbsExpectationBC G β J h Λ (minusConfig ι) (fun σ => Spin.sign ℝ (σ i)) ≤
        gibbsExpectationBC G β J h Λ η (fun σ => Spin.sign ℝ (σ i)) ∧
      gibbsExpectationBC G β J h Λ η (fun σ => Spin.sign ℝ (σ i)) ≤
        gibbsExpectationBC G β J h Λ (plusConfig ι) (fun σ => Spin.sign ℝ (σ i)) :=
  gibbsExpectationBC_extremal_sandwich G hβ hJ Λ η _ (singleSpinObs_monotone i)

end IsingModel
