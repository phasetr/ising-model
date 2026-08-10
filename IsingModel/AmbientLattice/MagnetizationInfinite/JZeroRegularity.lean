import IsingModel.AmbientLattice.MagnetizationInfinite.TrivialSlices

/-!
# Regularity of the infinite-volume magnetization on the noninteracting slice

Statements for an ambient graph `G : SimpleGraph V`, an exhaustion `Λ` of `V` and an ambient
site `i : V`, on the slice where the coupling is `0`.

Every declaration takes exactly two instance binders, `DecidableEq V` and the stagewise
`Fintype` instance on the edge set of the induced subgraph of `Λ.volume n`. The Prop-valued
hypotheses are exactly these: the field-direction statements assume `0 < β`, and the
inverse-temperature statements assume `0 ≤ h`; no declaration carries any other.

On that slice the infinite-volume magnetization has the closed form `Real.tanh (β * h)`. Under
either hypothesis the argument `β * h` is nonnegative, so the closed form takes values in
`Set.Ico 0 1` and vanishes exactly when `β * h = 0`. In the field direction, where `0 < β`,
that is exactly at `h = 0`. In the inverse-temperature direction, where `0 ≤ h` and the
inverse temperature ranges over `Set.Ioi 0`, the closed form is identically `0` when `h = 0`
and strictly positive throughout when `0 < h`.

Transporting continuity and differentiability of the closed form along that equality gives
continuity in the field on `Set.Ici 0`, differentiability in the field on `Set.Ioi 0`, and, in
the inverse temperature, continuity and differentiability on `Set.Ioi 0`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

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
