import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeMagnetization
import IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationFlipSymmetry
import IsingModel.Inequalities.MonotonicityField
import IsingModel.Concrete.LatticeGraphCorrelation.CubicBoxScreening

/-!
# Field monotonicity of the magnetization (FV §3.6, Issue #3599)

For a ferromagnetic Ising model, increasing the external field `h` increases the
magnetization.  This file lifts the field monotonicity of the unconditioned Gibbs
expectation (Holley's inequality, `gibbsExpectation_field_mono`) to the
**boundary-condition** Gibbs expectation (the `+` boundary case is what the
cubic-exhaustion magnetization is built from), then to the infinite-volume
magnetization `m^±(β,·)` by passing to the limit.

* `boltzmannWeightBC_field_cross_supermodular` — the field cross-supermodularity of
  the boundary-condition Boltzmann weights (the Holley hypothesis).
* `gibbsExpectationBC_field_mono` — field monotonicity of the `η`-boundary Gibbs
  expectation of a monotone observable.
* `plusMagnetization_mono_h` / `minusMagnetization_mono_h` — `m^±(β,·)` is
  nondecreasing in the field.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.6 (magnetization, monotonicity in the field; Holley's
inequality, Theorem 3.50).
-/

namespace IsingModel

open Finset Filter Topology

section BoundaryConditionFieldMonotonicity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Field cross-supermodularity of the boundary-condition Boltzmann weights**: for a
ferromagnetic uniform coupling and `h ≤ h'`,
`w^η_h(a)·w^η_{h'}(b) ≤ w^η_h(a ⊓ b)·w^η_{h'}(a ⊔ b)`.  When both `a, b` agree with
`η` off `Λ` the boundary-agreement sublattice closure (`agreesOff_inf` / `agreesOff_sup`)
reduces this to the unconditioned field cross-supermodularity; otherwise the left side
vanishes. -/
theorem boltzmannWeightBC_field_cross_supermodular (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J h h' : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hh : h ≤ h') (Λ : Finset ι) (η a b : Config ι) :
    boltzmannWeightBC G β (fun _ => J) h Λ η a * boltzmannWeightBC G β (fun _ => J) h' Λ η b ≤
      boltzmannWeightBC G β (fun _ => J) h Λ η (a ⊓ b) *
        boltzmannWeightBC G β (fun _ => J) h' Λ η (a ⊔ b) := by
  by_cases ha : agreesOff Λ η a
  · by_cases hb : agreesOff Λ η b
    · rw [boltzmannWeightBC_of_agrees G β (fun _ => J) h ha,
        boltzmannWeightBC_of_agrees G β (fun _ => J) h' hb,
        boltzmannWeightBC_of_agrees G β (fun _ => J) h (agreesOff_inf ha hb),
        boltzmannWeightBC_of_agrees G β (fun _ => J) h' (agreesOff_sup ha hb),
        boltzmannWeightJ_uniform_eq, boltzmannWeightJ_uniform_eq,
        boltzmannWeightJ_uniform_eq, boltzmannWeightJ_uniform_eq]
      exact boltzmannWeight_field_cross_supermodular G hβ hJ hh a b
    · rw [boltzmannWeightBC_of_not_agrees G β (fun _ => J) h' hb, mul_zero]
      exact mul_nonneg (boltzmannWeightBC_nonneg G β (fun _ => J) h Λ η _)
        (boltzmannWeightBC_nonneg G β (fun _ => J) h' Λ η _)
  · rw [boltzmannWeightBC_of_not_agrees G β (fun _ => J) h ha, zero_mul]
    exact mul_nonneg (boltzmannWeightBC_nonneg G β (fun _ => J) h Λ η _)
      (boltzmannWeightBC_nonneg G β (fun _ => J) h' Λ η _)

/-- **Field monotonicity of the boundary-condition Gibbs expectation, nonnegative
case** (Holley): for a ferromagnetic Ising model, `h ≤ h'`, and a nonnegative monotone
observable `φ`, `⟨φ⟩^η_h ≤ ⟨φ⟩^η_{h'}`. -/
theorem gibbsExpectationBC_field_mono_of_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J h h' : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hh : h ≤ h') (Λ : Finset ι) (η : Config ι)
    (φ : Config ι → ℝ) (hφ_nn : 0 ≤ φ) (hφ_mono : Monotone φ) :
    gibbsExpectationBC G β (fun _ => J) h Λ η φ ≤ gibbsExpectationBC G β (fun _ => J) h' Λ η φ := by
  classical
  set Zh := partitionFunctionBC G β (fun _ => J) h Λ η with hZh_def
  set Zh' := partitionFunctionBC G β (fun _ => J) h' Λ η with hZh'_def
  have hZh : 0 < Zh := partitionFunctionBC_pos G β (fun _ => J) h Λ η
  have hZh' : 0 < Zh' := partitionFunctionBC_pos G β (fun _ => J) h' Λ η
  set fm : Config ι → ℝ := fun σ => boltzmannWeightBC G β (fun _ => J) h Λ η σ / Zh
    with hfm_def
  set gm : Config ι → ℝ := fun σ => boltzmannWeightBC G β (fun _ => J) h' Λ η σ / Zh'
    with hgm_def
  have hfm_nn : 0 ≤ fm := fun σ =>
    div_nonneg (boltzmannWeightBC_nonneg G β (fun _ => J) h Λ η σ) hZh.le
  have hgm_nn : 0 ≤ gm := fun σ =>
    div_nonneg (boltzmannWeightBC_nonneg G β (fun _ => J) h' Λ η σ) hZh'.le
  have hsum_fm : ∑ σ : Config ι, fm σ = 1 := by
    simp only [hfm_def, div_eq_mul_inv, ← Finset.sum_mul]
    rw [show (∑ σ : Config ι, boltzmannWeightBC G β (fun _ => J) h Λ η σ) = Zh from rfl,
      mul_inv_cancel₀ (ne_of_gt hZh)]
  have hsum_gm : ∑ σ : Config ι, gm σ = 1 := by
    simp only [hgm_def, div_eq_mul_inv, ← Finset.sum_mul]
    rw [show (∑ σ : Config ι, boltzmannWeightBC G β (fun _ => J) h' Λ η σ) = Zh' from rfl,
      mul_inv_cancel₀ (ne_of_gt hZh')]
  have hfg : ∑ σ : Config ι, fm σ = ∑ σ : Config ι, gm σ := by rw [hsum_fm, hsum_gm]
  have hcross : ∀ a b : Config ι, fm a * gm b ≤ fm (a ⊓ b) * gm (a ⊔ b) := by
    intro a b
    simp only [hfm_def, hgm_def, div_mul_div_comm]
    exact (div_le_div_iff_of_pos_right (mul_pos hZh hZh')).mpr
      (boltzmannWeightBC_field_cross_supermodular G hβ hJ hh Λ η a b)
  have hhol := holley (μ := φ) (f := fm) (g := gm) hφ_nn hfm_nn hgm_nn hφ_mono hfg hcross
  have hEh : gibbsExpectationBC G β (fun _ => J) h Λ η φ = ∑ σ : Config ι, φ σ * fm σ := by
    unfold gibbsExpectationBC
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [hfm_def, hZh_def]
    rw [div_eq_inv_mul]; ring
  have hEh' : gibbsExpectationBC G β (fun _ => J) h' Λ η φ = ∑ σ : Config ι, φ σ * gm σ := by
    unfold gibbsExpectationBC
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [hgm_def, hZh'_def]
    rw [div_eq_inv_mul]; ring
  rw [hEh, hEh']
  exact hhol

/-- **Field monotonicity of the boundary-condition Gibbs expectation** (Holley): for a
ferromagnetic Ising model, `h ≤ h'`, and **any** monotone observable `φ` (of arbitrary
sign), `⟨φ⟩^η_h ≤ ⟨φ⟩^η_{h'}`.  Subtracts the finite minimum of `φ` to reduce to the
nonnegative case. -/
theorem gibbsExpectationBC_field_mono (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J h h' : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hh : h ≤ h') (Λ : Finset ι) (η : Config ι)
    (φ : Config ι → ℝ) (hφ_mono : Monotone φ) :
    gibbsExpectationBC G β (fun _ => J) h Λ η φ ≤ gibbsExpectationBC G β (fun _ => J) h' Λ η φ := by
  classical
  have huniv : (Finset.univ : Finset (Config ι)).Nonempty := Finset.univ_nonempty
  set c : ℝ := Finset.univ.inf' huniv φ with hc_def
  have hc : ∀ σ : Config ι, c ≤ φ σ := fun σ => Finset.inf'_le φ (Finset.mem_univ σ)
  set φ' : Config ι → ℝ := fun σ => φ σ - c with hφ'_def
  have hφ'_nn : 0 ≤ φ' := fun σ => sub_nonneg.mpr (hc σ)
  have hφ'_mono : Monotone φ' := fun x y hxy => sub_le_sub_right (hφ_mono hxy) c
  have hEh : gibbsExpectationBC G β (fun _ => J) h Λ η φ'
      = gibbsExpectationBC G β (fun _ => J) h Λ η φ - c := by
    have hrw : φ' = φ + (fun _ => -c) := by funext σ; simp [hφ'_def, Pi.add_apply]; ring
    rw [hrw, gibbsExpectationBC_add, gibbsExpectationBC_const]; ring
  have hEh' : gibbsExpectationBC G β (fun _ => J) h' Λ η φ'
      = gibbsExpectationBC G β (fun _ => J) h' Λ η φ - c := by
    have hrw : φ' = φ + (fun _ => -c) := by funext σ; simp [hφ'_def, Pi.add_apply]; ring
    rw [hrw, gibbsExpectationBC_add, gibbsExpectationBC_const]; ring
  have hmono := gibbsExpectationBC_field_mono_of_nonneg G hβ hJ hh Λ η φ' hφ'_nn hφ'_mono
  rw [hEh, hEh'] at hmono
  linarith

end BoundaryConditionFieldMonotonicity

namespace Ambient

open Finset Filter Topology

variable {d : ℕ}

/-- **Field monotonicity of the `+` magnetization** `m⁺(β,·)`: for `h ≤ h'`,
`m⁺(β,h) ≤ m⁺(β,h')` (increasing the field increases the magnetization).  Each
finite-volume `+` box magnetization is monotone in `h`
(`gibbsExpectationBC_field_mono` on the monotone single spin), and `m⁺` is their
limit. -/
theorem plusMagnetization_mono_h {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (x : Fin d → ℤ)
    {h h' : ℝ} (hh : h ≤ h') :
    plusMagnetization x J h β ≤ plusMagnetization x J h' β := by
  refine le_of_tendsto_of_tendsto' (tendsto_plusMagnetization (h := h) hβ hJ x)
    (tendsto_plusMagnetization (h := h') hβ hJ x) (fun k => ?_)
  unfold plusBoxObsExpectation plusBoxExpectation
  exact gibbsExpectationBC_field_mono _ hβ hJ hh _ _ _
    ((singleSpinMonoObs x).mono.comp (restrictConfig_monotone _))

/-- **Field monotonicity of the `−` magnetization** `m⁻(β,·)`: for `h ≤ h'`,
`m⁻(β,h) ≤ m⁻(β,h')` (via the flip symmetry `m⁻(β,h) = −m⁺(β,−h)` and the `+`
monotonicity). -/
theorem minusMagnetization_mono_h {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (x : Fin d → ℤ)
    {h h' : ℝ} (hh : h ≤ h') :
    minusMagnetization x J h β ≤ minusMagnetization x J h' β := by
  rw [minusMagnetization_eq_neg_plusMagnetization_neg_h hβ hJ,
    minusMagnetization_eq_neg_plusMagnetization_neg_h hβ hJ]
  exact neg_le_neg (plusMagnetization_mono_h hβ hJ x (neg_le_neg hh))

end Ambient

end IsingModel
