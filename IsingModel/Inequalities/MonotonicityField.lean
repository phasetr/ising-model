import IsingModel.Inequalities.FKG
import IsingModel.Inequalities.FKGGeneral
import Mathlib.Combinatorics.SetFamily.FourFunctions

/-!
# Monotonicity of the Gibbs expectation in the external field (Holley's inequality)

For a ferromagnetic Ising model, increasing the external field `h` increases the
Gibbs expectation of every monotone observable:

  `h ≤ h'  ⟹  ⟨f⟩_h ≤ ⟨f⟩_{h'}`   (for nondecreasing `f`).

This is a foundational monotonicity result (the basis of the stochastic ordering
of Ising measures, the `+`/`−` extremal states, and the infinite-volume limit).
It is proved via **Holley's inequality** (`Mathlib.Combinatorics.SetFamily.FourFunctions.holley`):
the two normalised Boltzmann weights at fields `h ≤ h'` satisfy the Holley
domination condition

  `w_h(σ)·w_{h'}(σ') ≤ w_h(σ ⊓ σ')·w_{h'}(σ ⊔ σ')`,

whose interaction part is the usual edge log-supermodularity and whose field part
is the per-site inequality `h·s(a) + h'·s(b) ≤ h·s(a⊓b) + h'·s(a⊔b)` valid for
`h ≤ h'`.

* `boltzmannWeight_field_cross_supermodular` — the Holley domination condition.
* `gibbsExpectation_field_mono_of_nonneg` — field monotonicity for nonnegative
  monotone observables.
* `gibbsExpectation_field_mono` — field monotonicity for arbitrary monotone
  observables (via the constant shift).

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
§3.6.2 (FKG) and the Holley inequality; Glimm–Jaffe, *Quantum Physics*, §4.1.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Per-edge spin supermodularity** (local copy for this file): `s(a)s(b) +
s(c)s(d) ≤ s(a⊔c)s(b⊔d) + s(a⊓c)s(b⊓d)`, by exhausting the 16 cases. -/
private theorem spin_edge_supermodular_F (a b c d : Spin) :
    Spin.sign ℝ a * Spin.sign ℝ b + Spin.sign ℝ c * Spin.sign ℝ d ≤
    Spin.sign ℝ (a ⊔ c) * Spin.sign ℝ (b ⊔ d) +
    Spin.sign ℝ (a ⊓ c) * Spin.sign ℝ (b ⊓ d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [Spin.sign, Spin.toSign]

/-- **Per-site field monotonicity**: for `h ≤ h'`,
`h·s(a) + h'·s(b) ≤ h·s(a⊓b) + h'·s(a⊔b)`.  Verified case by case on the two
spins; the only nontrivial case is `s(a) ≥ s(b)`, giving
`(h'−h)(s(a)−s(b)) ≥ 0`. -/
private theorem field_site_mono {h h' : ℝ} (hh : h ≤ h') (a b : Spin) :
    h * Spin.sign ℝ a + h' * Spin.sign ℝ b ≤
    h * Spin.sign ℝ (a ⊓ b) + h' * Spin.sign ℝ (a ⊔ b) := by
  cases a <;> cases b <;> simp [Spin.sign, Spin.toSign]
  all_goals linarith

omit [DecidableEq ι] in
/-- **Holley domination condition for the Ising field family**: for `β, J ≥ 0` and
`h ≤ h'`,

`w_h(a)·w_{h'}(b) ≤ w_h(a ⊓ b)·w_{h'}(a ⊔ b)`.

The interaction term is supermodular (edge supermodularity, weight `βJ ≥ 0`); the
field term is the per-site monotonicity `field_site_mono` (weight `β ≥ 0`). -/
theorem boltzmannWeight_field_cross_supermodular (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J h h' : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hh : h ≤ h') (a b : Config ι) :
    boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) a *
        boltzmannWeight G (⟨J, h', β⟩ : IsingParams ℝ) b ≤
      boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) (a ⊓ b) *
        boltzmannWeight G (⟨J, h', β⟩ : IsingParams ℝ) (a ⊔ b) := by
  unfold boltzmannWeight
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp_of_le
  unfold hamiltonian interactionEnergy externalFieldEnergy
  -- Edge supermodularity (same sum on both sides, ⊓/⊔ order).
  have hedge : ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) a e +
      ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) b e ≤
      ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) (a ⊓ b) e +
      ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) (a ⊔ b) e := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun e _ => ?_
    refine Sym2.ind (fun i j => ?_) e
    simp only [edgeSpin, Sym2.lift_mk, Pi.inf_apply, Pi.sup_apply, Spin.sign]
    have := spin_edge_supermodular_F (a i) (a j) (b i) (b j)
    -- s(a_i)s(a_j) + s(b_i)s(b_j) ≤ s(a_i⊔b_i)s(a_j⊔b_j) + s(a_i⊓b_i)s(a_j⊓b_j)
    simp only [Spin.sign] at this
    linarith [this]
  -- Field monotonicity (per site, weight β).
  have hfield : h * ∑ i : ι, Spin.sign ℝ (a i) + h' * ∑ i : ι, Spin.sign ℝ (b i) ≤
      h * ∑ i : ι, Spin.sign ℝ ((a ⊓ b) i) + h' * ∑ i : ι, Spin.sign ℝ ((a ⊔ b) i) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [Pi.inf_apply, Pi.sup_apply]
    exact field_site_mono hh (a i) (b i)
  have hedge_scaled := mul_le_mul_of_nonneg_left hedge (mul_nonneg hβ hJ)
  have hfield_scaled := mul_le_mul_of_nonneg_left hfield hβ
  nlinarith [hedge_scaled, hfield_scaled]

/-- **Field monotonicity of the Gibbs expectation, nonnegative case**: for a
ferromagnetic Ising model (`β, J ≥ 0`), `h ≤ h'`, and a nonnegative monotone
nondecreasing observable `φ`, `⟨φ⟩_h ≤ ⟨φ⟩_{h'}`.

Apply Holley's inequality to the two normalised Boltzmann weights, whose
domination condition is `boltzmannWeight_field_cross_supermodular`. -/
theorem gibbsExpectation_field_mono_of_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J h h' : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hh : h ≤ h')
    (φ : Config ι → ℝ) (hφ_nn : 0 ≤ φ) (hφ_mono : Monotone φ) :
    gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ) φ ≤
      gibbsExpectation G (⟨J, h', β⟩ : IsingParams ℝ) φ := by
  classical
  set Zh := partitionFunction G (⟨J, h, β⟩ : IsingParams ℝ) with hZh_def
  set Zh' := partitionFunction G (⟨J, h', β⟩ : IsingParams ℝ) with hZh'_def
  have hZh : 0 < Zh := partitionFunction_pos G _
  have hZh' : 0 < Zh' := partitionFunction_pos G _
  set fm : Config ι → ℝ := fun σ => boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ / Zh
    with hfm_def
  set gm : Config ι → ℝ := fun σ => boltzmannWeight G (⟨J, h', β⟩ : IsingParams ℝ) σ / Zh'
    with hgm_def
  have hfm_nn : 0 ≤ fm := fun σ => div_nonneg (boltzmannWeight_pos G _ σ).le hZh.le
  have hgm_nn : 0 ≤ gm := fun σ => div_nonneg (boltzmannWeight_pos G _ σ).le hZh'.le
  have hsum_fm : ∑ σ : Config ι, fm σ = 1 := by
    simp only [hfm_def, div_eq_mul_inv, ← Finset.sum_mul]
    rw [show (∑ σ : Config ι, boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ) = Zh from rfl,
      mul_inv_cancel₀ (ne_of_gt hZh)]
  have hsum_gm : ∑ σ : Config ι, gm σ = 1 := by
    simp only [hgm_def, div_eq_mul_inv, ← Finset.sum_mul]
    rw [show (∑ σ : Config ι, boltzmannWeight G (⟨J, h', β⟩ : IsingParams ℝ) σ) = Zh' from rfl,
      mul_inv_cancel₀ (ne_of_gt hZh')]
  have hfg : ∑ σ : Config ι, fm σ = ∑ σ : Config ι, gm σ := by rw [hsum_fm, hsum_gm]
  have hcross : ∀ a b : Config ι, fm a * gm b ≤ fm (a ⊓ b) * gm (a ⊔ b) := by
    intro a b
    simp only [hfm_def, hgm_def, div_mul_div_comm]
    exact (div_le_div_iff_of_pos_right (mul_pos hZh hZh')).mpr
      (boltzmannWeight_field_cross_supermodular G hβ hJ hh a b)
  have hhol := holley (μ := φ) (f := fm) (g := gm) hφ_nn hfm_nn hgm_nn hφ_mono hfg hcross
  -- `∑ φ·fm = ⟨φ⟩_h` and `∑ φ·gm = ⟨φ⟩_{h'}`.
  have hEh : gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ) φ = ∑ σ : Config ι, φ σ * fm σ := by
    unfold gibbsExpectation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [hfm_def, hZh_def]
    rw [div_eq_inv_mul]
    ring
  have hEh' : gibbsExpectation G (⟨J, h', β⟩ : IsingParams ℝ) φ = ∑ σ : Config ι, φ σ * gm σ := by
    unfold gibbsExpectation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [hgm_def, hZh'_def]
    rw [div_eq_inv_mul]
    ring
  rw [hEh, hEh']
  exact hhol

/-- **Field monotonicity of the Gibbs expectation** (Holley): for a ferromagnetic
Ising model (`β, J ≥ 0`), `h ≤ h'`, and **any** monotone nondecreasing observable
`φ` (of arbitrary sign), `⟨φ⟩_h ≤ ⟨φ⟩_{h'}`.

Drops the nonnegativity hypothesis of `gibbsExpectation_field_mono_of_nonneg`:
the inequality `⟨φ⟩_h ≤ ⟨φ⟩_{h'}` is invariant under shifting `φ` by a constant
(both sides change by the same constant, by normalisation `⟨1⟩ = 1`), so subtract
the finite minimum of `φ` to reduce to the nonnegative case. -/
theorem gibbsExpectation_field_mono (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J h h' : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hh : h ≤ h')
    (φ : Config ι → ℝ) (hφ_mono : Monotone φ) :
    gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ) φ ≤
      gibbsExpectation G (⟨J, h', β⟩ : IsingParams ℝ) φ := by
  classical
  have huniv : (Finset.univ : Finset (Config ι)).Nonempty := Finset.univ_nonempty
  set c : ℝ := Finset.univ.inf' huniv φ with hc_def
  have hc : ∀ σ : Config ι, c ≤ φ σ := fun σ => Finset.inf'_le φ (Finset.mem_univ σ)
  set φ' : Config ι → ℝ := fun σ => φ σ - c with hφ'_def
  have hφ'_nn : 0 ≤ φ' := fun σ => sub_nonneg.mpr (hc σ)
  have hφ'_mono : Monotone φ' := fun x y hxy => sub_le_sub_right (hφ_mono hxy) c
  have hEh : gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ) φ'
      = gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ) φ - c := by
    have hrw : φ' = φ + (fun _ => -c) := by funext σ; simp [hφ'_def, Pi.add_apply]; ring
    rw [hrw, gibbsExpectation_add, gibbsExpectation_const]; ring
  have hEh' : gibbsExpectation G (⟨J, h', β⟩ : IsingParams ℝ) φ'
      = gibbsExpectation G (⟨J, h', β⟩ : IsingParams ℝ) φ - c := by
    have hrw : φ' = φ + (fun _ => -c) := by funext σ; simp [hφ'_def, Pi.add_apply]; ring
    rw [hrw, gibbsExpectation_add, gibbsExpectation_const]; ring
  have hmono := gibbsExpectation_field_mono_of_nonneg G hβ hJ hh φ' hφ'_nn hφ'_mono
  rw [hEh, hEh'] at hmono
  linarith [hmono]

end IsingModel
