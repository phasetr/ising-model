import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.MagnetizationInfiniteLambdaHSymmetry
import IsingModel.AmbientLattice.MagnetizationInfiniteExhaustionHSymmetry
import IsingModel.AmbientLattice.MagnetizationInfiniteSusceptibility

/-!
# Ambient susceptibilityInfinite regularity at J = 0

Narrow child module for the susceptibilityInfinite J = 0 closed form +
trivial-slice + regularity-at-J=0 wrappers (7 theorems):
`susceptibilityInfinite_J_zero`, `susceptibilityInfinite_beta_zero`,
`susceptibilityInfinite_zero_params`,
`susceptibilityInfinite_continuousOn_field_J_zero`,
`susceptibilityInfinite_continuousOn_beta_J_zero`,
`susceptibilityInfinite_differentiableOn_field_J_zero`,
`susceptibilityInfinite_differentiableOn_beta_J_zero`. The theorem
names are unchanged from the former `MagnetizationInfinite`
declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **`susceptibilityInfinite` at `J = 0` closed form** (Step 259, GJ §17.1):
the infinite-volume susceptibility at `J = 0` reduces to the
single-site (non-interacting) closed-form value
`tanh(β·h) * (1 - tanh(β·h))`.

**Proof**: at `J = 0` the system is non-interacting, so each site contributes
independently. By `susceptibility_J_zero`, the finite-volume susceptibility on
`inducedGraph G (Λ.volume n)` (for any `n` with `i ∈ Λ.volume n`) equals the
closed-form value. For `n` with `i ∉ Λ.volume n`, the along-exhaustion susceptibility
vanishes. Taking the `ciSup`: the sequence is eventually constant at the closed-form
value (by `Exhaustion.exhaust` applied to `{i}`), hence the sup equals that value.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.1 (non-interacting `J = 0`
slice); §5.1 pp. 76–77 (susceptibility). -/
theorem susceptibilityInfinite_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : V) :
    susceptibilityInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i
      = Real.tanh (β * h) * (1 - Real.tanh (β * h)) := by
  -- Per-stage value: closed form when i ∈ Λ_n, 0 otherwise
  have h_per_stage : ∀ n : ℕ,
      susceptibilityAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) i n =
      if i ∈ Λ.volume n then Real.tanh (β * h) * (1 - Real.tanh (β * h)) else 0 := by
    intro n
    by_cases hi : i ∈ Λ.volume n
    · rw [if_pos hi, susceptibilityAlongExhaustion_of_mem G Λ _ hi,
          susceptibilityΛ_apply]
      exact IsingModel.susceptibility_J_zero
        (inducedGraph G (Λ.volume n)) h β ⟨i, hi⟩
    · rw [if_neg hi, susceptibilityAlongExhaustion_of_not_mem G Λ _ hi]
  -- Rewrite the susceptibilityInfinite as ciSup
  rw [susceptibilityInfinite_eq_ciSup]
  -- Use eventually constant argument: pick N with i ∈ Λ_N, then sequence is constant
  -- from N onwards (= closed form value).
  obtain ⟨N, hN⟩ := Λ.exhaust ({i} : Finset V)
  set c : ℝ := Real.tanh (β * h) * (1 - Real.tanh (β * h)) with hc_def
  -- Claim: ⨆ n, susceptibilityAlongExhaustion ... i n = c
  -- Helper: 0 ≤ c (under ferromagnetic h ≥ 0, β > 0)
  have hc_nn : 0 ≤ c := by
    obtain ⟨_, hh, hβ_pos⟩ := hf
    have hβh_nn : 0 ≤ β * h := mul_nonneg hβ_pos.le hh
    have htanh_nn : 0 ≤ Real.tanh (β * h) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr hβh_nn) (Real.cosh_pos _).le
    have htanh_le_one : Real.tanh (β * h) ≤ 1 := (Real.tanh_lt_one _).le
    exact mul_nonneg htanh_nn (by linarith)
  apply le_antisymm
  · -- ≤ c: every term is ≤ c
    apply ciSup_le
    intro n
    rw [h_per_stage n]
    by_cases hi : i ∈ Λ.volume n
    · rw [if_pos hi]
    · rw [if_neg hi]
      exact hc_nn
  · -- ≥ c: pick the term at n = N where i ∈ Λ_N
    have hi_N : i ∈ Λ.volume N := by
      have := hN N le_rfl
      simpa using this
    have h_bdd : BddAbove (Set.range
        (fun n => susceptibilityAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) i n)) := by
      refine ⟨c, ?_⟩
      rintro x ⟨n, hx⟩
      simp only at hx
      rw [← hx, h_per_stage n]
      by_cases hi : i ∈ Λ.volume n
      · rw [if_pos hi]
      · rw [if_neg hi]
        exact hc_nn
    refine le_ciSup_of_le h_bdd N ?_
    rw [h_per_stage N, if_pos hi_N]

/-- **`susceptibilityInfinite` at `β = 0` vanishes** (Step 260):
At infinite temperature, every truncated 2-point function vanishes
(`truncated2_beta_zero`), so the finite-volume susceptibility is zero
on each induced graph. The supremum of zeros is zero. -/
theorem susceptibilityInfinite_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : V) :
    susceptibilityInfinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ) i = 0 := by
  rw [susceptibilityInfinite_eq_ciSup]
  -- Each susceptibilityAlongExhaustion = 0
  have h_zero : ∀ n,
      susceptibilityAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ) i n = 0 := by
    intro n
    by_cases hi : i ∈ Λ.volume n
    · rw [susceptibilityAlongExhaustion_of_mem G Λ _ hi, susceptibilityΛ_apply]
      exact IsingModel.susceptibility_beta_zero
        (inducedGraph G (Λ.volume n)) J h ⟨i, hi⟩
    · rw [susceptibilityAlongExhaustion_of_not_mem G Λ _ hi]
  simp only [h_zero]
  exact ciSup_const

/-- **`susceptibilityInfinite` at `J = h = 0` vanishes** (Step 260):
At zero coupling and zero field, the system is uncoupled and at unit Boltzmann
weight; truncated 2-point vanishes for non-trivial finsets and the susceptibility
is zero. Specialization of `susceptibilityInfinite_J_zero` at `h = 0` (where
`tanh(β·0)·(1 - tanh(β·0)) = 0·1 = 0`). -/
theorem susceptibilityInfinite_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (hβ : 0 < β) (i : V) :
    susceptibilityInfinite G Λ (⟨0, 0, β⟩ : IsingParams ℝ) i = 0 := by
  have hf : Ferromagnetic (⟨(0 : ℝ), 0, β⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, le_refl 0, hβ⟩
  rw [susceptibilityInfinite_J_zero G Λ 0 β hf i]
  simp

/-- **`susceptibilityInfinite` continuous in h on `Ici 0` at J = 0** (Step 262):
For `0 < β`, the function `h ↦ susceptibilityInfinite G Λ ⟨0, h, β⟩ i`
equals `tanh(β·h)·(1 - tanh(β·h))` on `Ici 0` (Step 259), which is continuous.

Reference: Glimm–Jaffe §17.6 (susceptibility regularity at non-interacting slice). -/
theorem susceptibilityInfinite_continuousOn_field_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (hβ : 0 < β) (i : V) :
    ContinuousOn
      (fun h => susceptibilityInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i)
      (Set.Ici (0 : ℝ)) := by
  -- On Ici 0, the function equals tanh(βh)·(1 - tanh(βh)) by Step 259
  have hF_eq : ∀ h ∈ Set.Ici (0 : ℝ),
      susceptibilityInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i
        = Real.tanh (β * h) * (1 - Real.tanh (β * h)) := by
    intro h hh_in
    have hh_nn : 0 ≤ h := hh_in
    have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
      ⟨le_refl 0, hh_nn, hβ⟩
    exact susceptibilityInfinite_J_zero G Λ h β hf i
  -- ContinuousOn via congrEq + continuity of tanh·(1-tanh)
  have h_tanh_cont : Continuous (Real.tanh : ℝ → ℝ) := by
    rw [show (Real.tanh : ℝ → ℝ) = (fun x => Real.sinh x / Real.cosh x) from
        funext fun x => Real.tanh_eq_sinh_div_cosh x]
    exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
  have h_cont_outer : Continuous (fun h : ℝ => Real.tanh (β * h) * (1 - Real.tanh (β * h))) :=
    (h_tanh_cont.comp (continuous_const.mul continuous_id)).mul
      (continuous_const.sub
        (h_tanh_cont.comp (continuous_const.mul continuous_id)))
  exact h_cont_outer.continuousOn.congr (fun h hh_in => hF_eq h hh_in)

/-- **`susceptibilityInfinite` ContinuousOn β on `Ioi 0` at J = 0** (Step 263):
For `0 ≤ h`, the function `β ↦ susceptibilityInfinite G Λ ⟨0, h, β⟩ i`
equals `tanh(β·h)·(1 - tanh(β·h))` on `Ioi 0` (Step 259), which is continuous.

Reference: Glimm–Jaffe §17.6. -/
theorem susceptibilityInfinite_continuousOn_beta_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h : ℝ) (hh_nn : 0 ≤ h) (i : V) :
    ContinuousOn
      (fun β => susceptibilityInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i)
      (Set.Ioi (0 : ℝ)) := by
  have hF_eq : ∀ β ∈ Set.Ioi (0 : ℝ),
      susceptibilityInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i
        = Real.tanh (β * h) * (1 - Real.tanh (β * h)) := by
    intro β hβ_in
    have hβ_pos : 0 < β := hβ_in
    have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
      ⟨le_refl 0, hh_nn, hβ_pos⟩
    exact susceptibilityInfinite_J_zero G Λ h β hf i
  have h_tanh_cont : Continuous (Real.tanh : ℝ → ℝ) := by
    rw [show (Real.tanh : ℝ → ℝ) = (fun x => Real.sinh x / Real.cosh x) from
        funext fun x => Real.tanh_eq_sinh_div_cosh x]
    exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
  have h_cont_outer : Continuous (fun β : ℝ => Real.tanh (β * h) * (1 - Real.tanh (β * h))) :=
    (h_tanh_cont.comp (continuous_id.mul continuous_const)).mul
      (continuous_const.sub
        (h_tanh_cont.comp (continuous_id.mul continuous_const)))
  exact h_cont_outer.continuousOn.congr (fun β hβ_in => hF_eq β hβ_in)

/-- **`susceptibilityInfinite` DifferentiableOn h on `Ioi 0` at J = 0** (Step 264). -/
theorem susceptibilityInfinite_differentiableOn_field_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (hβ : 0 < β) (i : V) :
    DifferentiableOn ℝ
      (fun h => susceptibilityInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i)
      (Set.Ioi (0 : ℝ)) := by
  have hF_eq : ∀ h ∈ Set.Ioi (0 : ℝ),
      susceptibilityInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i
        = Real.tanh (β * h) * (1 - Real.tanh (β * h)) := by
    intro h hh_in
    have hh_pos : 0 < h := hh_in
    have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
      ⟨le_refl 0, hh_pos.le, hβ⟩
    exact susceptibilityInfinite_J_zero G Λ h β hf i
  have h_tanh_diff : Differentiable ℝ (Real.tanh : ℝ → ℝ) := by
    rw [show (Real.tanh : ℝ → ℝ) = (fun x => Real.sinh x / Real.cosh x) from
        funext fun x => Real.tanh_eq_sinh_div_cosh x]
    exact Real.differentiable_sinh.div Real.differentiable_cosh (fun x => (Real.cosh_pos x).ne')
  have h_diff_outer :
      Differentiable ℝ (fun h : ℝ => Real.tanh (β * h) * (1 - Real.tanh (β * h))) :=
    (h_tanh_diff.comp (differentiable_const _ |>.mul differentiable_id)).mul
      ((differentiable_const _).sub
        (h_tanh_diff.comp (differentiable_const _ |>.mul differentiable_id)))
  exact (h_diff_outer.differentiableOn).congr (fun h hh_in => hF_eq h hh_in)

/-- **`susceptibilityInfinite` DifferentiableOn β on `Ioi 0` at J = 0** (Step 264). -/
theorem susceptibilityInfinite_differentiableOn_beta_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h : ℝ) (hh_nn : 0 ≤ h) (i : V) :
    DifferentiableOn ℝ
      (fun β => susceptibilityInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i)
      (Set.Ioi (0 : ℝ)) := by
  have hF_eq : ∀ β ∈ Set.Ioi (0 : ℝ),
      susceptibilityInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i
        = Real.tanh (β * h) * (1 - Real.tanh (β * h)) := by
    intro β hβ_in
    have hβ_pos : 0 < β := hβ_in
    have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
      ⟨le_refl 0, hh_nn, hβ_pos⟩
    exact susceptibilityInfinite_J_zero G Λ h β hf i
  have h_tanh_diff : Differentiable ℝ (Real.tanh : ℝ → ℝ) := by
    rw [show (Real.tanh : ℝ → ℝ) = (fun x => Real.sinh x / Real.cosh x) from
        funext fun x => Real.tanh_eq_sinh_div_cosh x]
    exact Real.differentiable_sinh.div Real.differentiable_cosh (fun x => (Real.cosh_pos x).ne')
  have h_diff_outer :
      Differentiable ℝ (fun β : ℝ => Real.tanh (β * h) * (1 - Real.tanh (β * h))) :=
    (h_tanh_diff.comp (differentiable_id.mul (differentiable_const _))).mul
      ((differentiable_const _).sub
        (h_tanh_diff.comp (differentiable_id.mul (differentiable_const _))))
  exact (h_diff_outer.differentiableOn).congr (fun β hβ_in => hF_eq β hβ_in)


end Ambient

end IsingModel
