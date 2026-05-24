import IsingModel.AmbientLattice.MagnetizationInfinite.TrivialSlices

/-!
# Infinite-volume magnetization regularity at J = 0

Continuity and differentiability wrappers for `magnetizationInfinite` on the
noninteracting `J = 0` slice.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Moved: susceptibilityInfinite J = 0 closed form + regularity at J = 0

The 7 susceptibilityInfinite J = 0 closed form + trivial-slice +
regularity-at-J=0 wrappers now live in
`IsingModel.AmbientLattice.MagnetizationInfiniteSusceptibilityRegularity`.
The earlier import path is preserved by re-importing the new child.
-/

/-- **`magnetizationInfinite` ContinuousOn h on Ici 0 at J = 0** (Step 266):
For `0 < β`, `h ↦ magnetizationInfinite ⟨0, h, β⟩ i = tanh(β·h)` (Step 233's
`magnetizationInfinite_J_zero`), which is continuous. -/
theorem magnetizationInfinite_continuousOn_field_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (hβ : 0 < β) (i : V) :
    ContinuousOn
      (fun h => magnetizationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i)
      (Set.Ici (0 : ℝ)) := by
  have hF_eq : ∀ h ∈ Set.Ici (0 : ℝ),
      magnetizationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) := by
    intro h hh_in
    have hh_nn : 0 ≤ h := hh_in
    have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
      ⟨le_refl 0, hh_nn, hβ⟩
    exact magnetizationInfinite_J_zero G Λ h β hf i
  have h_tanh_cont : Continuous (Real.tanh : ℝ → ℝ) := by
    rw [show (Real.tanh : ℝ → ℝ) = (fun x => Real.sinh x / Real.cosh x) from
        funext fun x => Real.tanh_eq_sinh_div_cosh x]
    exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
  have h_cont : Continuous (fun h : ℝ => Real.tanh (β * h)) :=
    h_tanh_cont.comp (continuous_const.mul continuous_id)
  exact h_cont.continuousOn.congr (fun h hh_in => hF_eq h hh_in)

/-- **`magnetizationInfinite` ContinuousOn β on Ioi 0 at J = 0** (Step 266). -/
theorem magnetizationInfinite_continuousOn_beta_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h : ℝ) (hh_nn : 0 ≤ h) (i : V) :
    ContinuousOn
      (fun β => magnetizationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i)
      (Set.Ioi (0 : ℝ)) := by
  have hF_eq : ∀ β ∈ Set.Ioi (0 : ℝ),
      magnetizationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) := by
    intro β hβ_in
    have hβ_pos : 0 < β := hβ_in
    have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
      ⟨le_refl 0, hh_nn, hβ_pos⟩
    exact magnetizationInfinite_J_zero G Λ h β hf i
  have h_tanh_cont : Continuous (Real.tanh : ℝ → ℝ) := by
    rw [show (Real.tanh : ℝ → ℝ) = (fun x => Real.sinh x / Real.cosh x) from
        funext fun x => Real.tanh_eq_sinh_div_cosh x]
    exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
  have h_cont : Continuous (fun β : ℝ => Real.tanh (β * h)) :=
    h_tanh_cont.comp (continuous_id.mul continuous_const)
  exact h_cont.continuousOn.congr (fun β hβ_in => hF_eq β hβ_in)

/-- **`magnetizationInfinite` DifferentiableOn h on Ioi 0 at J = 0** (Step 266). -/
theorem magnetizationInfinite_differentiableOn_field_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (hβ : 0 < β) (i : V) :
    DifferentiableOn ℝ
      (fun h => magnetizationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i)
      (Set.Ioi (0 : ℝ)) := by
  have hF_eq : ∀ h ∈ Set.Ioi (0 : ℝ),
      magnetizationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) := by
    intro h hh_in
    have hh_pos : 0 < h := hh_in
    have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
      ⟨le_refl 0, hh_pos.le, hβ⟩
    exact magnetizationInfinite_J_zero G Λ h β hf i
  have h_tanh_diff : Differentiable ℝ (Real.tanh : ℝ → ℝ) := by
    rw [show (Real.tanh : ℝ → ℝ) = (fun x => Real.sinh x / Real.cosh x) from
        funext fun x => Real.tanh_eq_sinh_div_cosh x]
    exact Real.differentiable_sinh.div Real.differentiable_cosh (fun x => (Real.cosh_pos x).ne')
  have h_diff : Differentiable ℝ (fun h : ℝ => Real.tanh (β * h)) :=
    h_tanh_diff.comp ((differentiable_const _).mul differentiable_id)
  exact h_diff.differentiableOn.congr (fun h hh_in => hF_eq h hh_in)

/-- **`magnetizationInfinite` DifferentiableOn β on Ioi 0 at J = 0** (Step 266). -/
theorem magnetizationInfinite_differentiableOn_beta_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h : ℝ) (hh_nn : 0 ≤ h) (i : V) :
    DifferentiableOn ℝ
      (fun β => magnetizationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i)
      (Set.Ioi (0 : ℝ)) := by
  have hF_eq : ∀ β ∈ Set.Ioi (0 : ℝ),
      magnetizationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) := by
    intro β hβ_in
    have hβ_pos : 0 < β := hβ_in
    have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
      ⟨le_refl 0, hh_nn, hβ_pos⟩
    exact magnetizationInfinite_J_zero G Λ h β hf i
  have h_tanh_diff : Differentiable ℝ (Real.tanh : ℝ → ℝ) := by
    rw [show (Real.tanh : ℝ → ℝ) = (fun x => Real.sinh x / Real.cosh x) from
        funext fun x => Real.tanh_eq_sinh_div_cosh x]
    exact Real.differentiable_sinh.div Real.differentiable_cosh (fun x => (Real.cosh_pos x).ne')
  have h_diff : Differentiable ℝ (fun β : ℝ => Real.tanh (β * h)) :=
    h_tanh_diff.comp (differentiable_id.mul (differentiable_const _))
  exact h_diff.differentiableOn.congr (fun β hβ_in => hF_eq β hβ_in)

end Ambient
end IsingModel
