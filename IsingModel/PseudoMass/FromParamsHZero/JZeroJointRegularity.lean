import IsingModel.PseudoMass.FromParamsHZero.JZeroHRegularity

/-!
# Pseudo-mass J-zero joint regularity

Joint continuity and differentiability wrappers in `(β, h)` on the `J = 0`
distinct-pair slice.

## Umbrella-reachable via its cluster head

This module has no importers outside its own cluster.  The cluster head is
registered in the root umbrella `IsingModel.lean`, so this module too lies
inside the transitive import closure of `import IsingModel` — the prerequisite
for the capstone axiom audit (`scripts/audit_gate.py`, check V3) to reach it.
Note that V3 inspects only the names listed in `scripts/audit/capstones.txt`,
and no declaration of this module is currently listed there.  It is
genuine formalization — non-trivial regularity results for the `J = 0` /
`h = 0` slices of `pseudoMassFromParamsAtPair`, built on the
`PseudoMass/FromParamsBasic` results.
-/

namespace IsingModel

open Set Real Filter

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is jointly
`DifferentiableAt` in `(β, h)` for `β > 0, h > 0`**: composition of
`(β, h) ↦ β·h` (joint differentiable) with `pseudoMassExt(tanh(t)^2)`
differentiable at `β·h > 0` (PR #1685). -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableAt_betaH_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    DifferentiableAt ℝ
      (fun p : ℝ × ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                          (⟨0, p.2, p.1⟩ : IsingParams ℝ) x z) (β, h) := by
  have hf_at : ∀ p : ℝ × ℝ, 0 < p.1 → 0 < p.2 →
                  Ferromagnetic (⟨(0 : ℝ), p.2, p.1⟩ : IsingParams ℝ) :=
    fun p hp1 hp2 => ⟨le_refl 0, hp2.le, hp1⟩
  have hβ_nhd : ∀ᶠ p : ℝ × ℝ in nhds (β, h), 0 < p.1 ∧ 0 < p.2 := by
    have h1 : ∀ᶠ p : ℝ × ℝ in nhds (β, h), 0 < p.1 := by
      have hcont : ContinuousAt (fun p : ℝ × ℝ => p.1) (β, h) :=
        continuous_fst.continuousAt
      exact hcont.eventually_const_lt hβ
    have h2 : ∀ᶠ p : ℝ × ℝ in nhds (β, h), 0 < p.2 := by
      have hcont : ContinuousAt (fun p : ℝ × ℝ => p.2) (β, h) :=
        continuous_snd.continuousAt
      exact hcont.eventually_const_lt hh
    filter_upwards [h1, h2] with p hp1 hp2 using ⟨hp1, hp2⟩
  have hEq : (fun p : ℝ × ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                                  (⟨0, p.2, p.1⟩ : IsingParams ℝ) x z) =ᶠ[nhds (β, h)]
              (fun p : ℝ × ℝ => pseudoMassExt hα hr (Real.tanh (p.1 * p.2) ^ 2)) := by
    filter_upwards [hβ_nhd] with p ⟨hp1, hp2⟩
    exact pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ
            (hf_at p hp1 hp2) hxz
  have hdiff_alt : DifferentiableAt ℝ
                    (fun p : ℝ × ℝ => pseudoMassExt hα hr
                      (Real.tanh (p.1 * p.2) ^ 2)) (β, h) := by
    have hβh_pos : 0 < β * h := mul_pos hβ hh
    have hmul : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 * p.2) (β, h) :=
      (differentiable_fst.mul differentiable_snd).differentiableAt
    have houter : DifferentiableAt ℝ
                    (fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) (β * h) :=
      pseudoMassExt_tanh_sq_differentiableAt_pos hα hr hβh_pos
    change DifferentiableAt ℝ
      ((fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) ∘
        (fun p : ℝ × ℝ => p.1 * p.2)) (β, h)
    exact DifferentiableAt.comp (β, h) houter hmul
  exact hdiff_alt.congr_of_eventuallyEq hEq

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is jointly
`ContinuousAt` in `(β, h)` for `β > 0, h > 0`**: composition of
`(β, h) ↦ β·h` (joint continuous) with `pseudoMassExt(tanh(t)^2)`
continuous at `β·h > 0` (PR #1685). -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousAt_betaH_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ContinuousAt
      (fun p : ℝ × ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                          (⟨0, p.2, p.1⟩ : IsingParams ℝ) x z) (β, h) := by
  have hf_at : ∀ p : ℝ × ℝ, 0 < p.1 → 0 < p.2 →
                  Ferromagnetic (⟨(0 : ℝ), p.2, p.1⟩ : IsingParams ℝ) :=
    fun p hp1 hp2 => ⟨le_refl 0, hp2.le, hp1⟩
  have hβ_nhd : ∀ᶠ p : ℝ × ℝ in nhds (β, h), 0 < p.1 ∧ 0 < p.2 := by
    have h1 : ∀ᶠ p : ℝ × ℝ in nhds (β, h), 0 < p.1 := by
      have hcont : ContinuousAt (fun p : ℝ × ℝ => p.1) (β, h) :=
        continuous_fst.continuousAt
      exact hcont.eventually_const_lt hβ
    have h2 : ∀ᶠ p : ℝ × ℝ in nhds (β, h), 0 < p.2 := by
      have hcont : ContinuousAt (fun p : ℝ × ℝ => p.2) (β, h) :=
        continuous_snd.continuousAt
      exact hcont.eventually_const_lt hh
    filter_upwards [h1, h2] with p hp1 hp2 using ⟨hp1, hp2⟩
  have hEq : (fun p : ℝ × ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                                  (⟨0, p.2, p.1⟩ : IsingParams ℝ) x z) =ᶠ[nhds (β, h)]
              (fun p : ℝ × ℝ => pseudoMassExt hα hr (Real.tanh (p.1 * p.2) ^ 2)) := by
    filter_upwards [hβ_nhd] with p ⟨hp1, hp2⟩
    exact pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ
            (hf_at p hp1 hp2) hxz
  refine (ContinuousAt.congr ?_ hEq.symm)
  have hβh_pos : 0 < β * h := mul_pos hβ hh
  have hmul : ContinuousAt (fun p : ℝ × ℝ => p.1 * p.2) (β, h) :=
    (continuous_fst.mul continuous_snd).continuousAt
  have houter : ContinuousAt
                  (fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) (β * h) :=
    pseudoMassExt_tanh_sq_continuousAt_pos hα hr hβh_pos
  change ContinuousAt
    ((fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) ∘
      (fun p : ℝ × ℝ => p.1 * p.2)) (β, h)
  exact ContinuousAt.comp houter hmul

end IsingModel
