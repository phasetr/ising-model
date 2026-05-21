import IsingModel.PseudoMass.FromParamsBasic

/-!
# Pseudo-Mass h-zero Parameter Specializations

This module is part of the split `IsingModel.PseudoMass` development.
-/

namespace IsingModel

open Set Real Filter

/-! ### `h = 0` specialisations using `truncated2Infinite`

At zero external field, `correlationInfinite ⟨J, 0, β⟩ {x, z} = truncated2Infinite ⟨J, 0, β⟩ x z`
(spin-flip Z₂ symmetry forces the singleton magnetisations to vanish), so the
`*_of_corr_*` family of bounds for `pseudoMassFromParamsAtPair` translates to
the corresponding `*_of_truncated2_*` form in terms of the function
`latticeMass` is actually defined against.
-/

/-- **At `h = 0`, `pseudoMassFromParamsAtPair ≤ pseudoMassExt(c_min)` from
`c_min ≤ truncated2`**: h = 0 specialisation of `_le_of_corr_ge` using the
identity `correlationInfinite ⟨J, 0, β⟩ {x,z} = truncated2Infinite ⟨J,0,β⟩ x z`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_le_of_truncated2_ge {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c_min : ℝ} (hc_min : c_min ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2)
    (hge : c_min ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      pseudoMassExt hα hr c_min := by
  have hbridge := Ambient.truncated2Infinite_h_zero
    (IsingModel.latticeGraph d) Λ J β x z
  rw [hbridge] at htrunc hge
  exact pseudoMassFromParamsAtPair_le_of_corr_ge hα hr d Λ
    (⟨J, 0, β⟩ : IsingParams ℝ) x z hc_min htrunc hge

/-- **At `h = 0`, `pseudoMassExt(c_max) ≤ pseudoMassFromParamsAtPair` from
`truncated2 ≤ c_max`**: h = 0 specialisation of `_ge_of_corr_le`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_ge_of_truncated2_le {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c_max : ℝ} (hc_max : c_max ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2)
    (hle : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ c_max) :
    pseudoMassExt hα hr c_max ≤
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  have hbridge := Ambient.truncated2Infinite_h_zero
    (IsingModel.latticeGraph d) Λ J β x z
  rw [hbridge] at htrunc hle
  exact pseudoMassFromParamsAtPair_ge_of_corr_le hα hr d Λ
    (⟨J, 0, β⟩ : IsingParams ℝ) x z hc_max htrunc hle

/-- **At `h = 0`, `pseudoMassFromParamsAtPair` sandwich** combining
`_le_of_truncated2_ge` and `_ge_of_truncated2_le`: if
`c_min ≤ truncated2 ≤ c_max` with all values in `Ioo 0 2`, then
`pseudoMassExt(c_max) ≤ pseudoMassFromParamsAtPair ≤ pseudoMassExt(c_min)`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_sandwich_of_truncated2_mem
    {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c_min c_max : ℝ}
    (hc_min : c_min ∈ Set.Ioo (0 : ℝ) 2)
    (hc_max : c_max ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2)
    (hge : c_min ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hle : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ c_max) :
    pseudoMassExt hα hr c_max ≤
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ∧
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      pseudoMassExt hα hr c_min :=
  ⟨pseudoMassFromParamsAtPair_at_h_zero_ge_of_truncated2_le
      hα hr d Λ J β x z hc_max htrunc hle,
   pseudoMassFromParamsAtPair_at_h_zero_le_of_truncated2_ge
      hα hr d Λ J β x z hc_min htrunc hge⟩

/-- **At `h = 0`, when `truncated2Infinite ∈ Ioo 0 2`, the bridge equals
the underlying `pseudoMass`** (not the totalised `pseudoMassExt`):
combining `pseudoMassFromParamsAtPair_at_h_zero_eq` (PR #1669) with
`pseudoMassExt_of_mem`. This gives access to the implicit-function-theorem
derivative API of `pseudoMass` (`HasStrictDerivAt`, etc.) when reasoning
about the bridge in the high-temperature ferromagnetic regime where
truncated2 is positive but bounded by 1. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z =
      pseudoMass hα hr htrunc := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq hα hr d Λ J β x z]
  exact pseudoMassExt_of_mem hα hr htrunc

/-- **At `h = 0`, the bridge as a `pseudoMass` upper bound from a
`truncated2` lower bound**: combining `_at_h_zero_le_of_truncated2_ge`
(PR #1671, gives `≤ pseudoMassExt(c_min)`) with `pseudoMassExt_of_mem`
(reduces to `pseudoMass(c_min)` when `c_min ∈ Ioo 0 2`). Useful for
deriving the §17.5 lower-bound `pseudoMass(...) ≤ latticeMass(...)`
direction. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_le_pseudoMass_of_truncated2_ge
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c_min : ℝ} (hc_min : c_min ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2)
    (hge : c_min ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      pseudoMass hα hr hc_min := by
  have hbound := pseudoMassFromParamsAtPair_at_h_zero_le_of_truncated2_ge
                    hα hr d Λ J β x z hc_min htrunc hge
  rwa [pseudoMassExt_of_mem hα hr hc_min] at hbound

/-- **At `h = 0`, the bridge as a `pseudoMass` lower bound from a
`truncated2` upper bound**: combining `_at_h_zero_ge_of_truncated2_le`
with `pseudoMassExt_of_mem`. Companion to
`_at_h_zero_le_pseudoMass_of_truncated2_ge`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_of_truncated2_le
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c_max : ℝ} (hc_max : c_max ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2)
    (hle : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ c_max) :
    pseudoMass hα hr hc_max ≤
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  have hbound := pseudoMassFromParamsAtPair_at_h_zero_ge_of_truncated2_le
                    hα hr d Λ J β x z hc_max htrunc hle
  rwa [pseudoMassExt_of_mem hα hr hc_max] at hbound

/-- **At `h = 0`, `pseudoMassFromParamsAtPair > 0` from `truncated2 ∈ Ioo 0 2`**:
direct corollary of `_at_h_zero_eq_pseudoMass_of_truncated2_mem` (PR #1672)
+ `pseudoMass_pos` (PR #928 Step 117g). When the truncated 2-point function
falls in the regime `(0, 2)`, the bridge is strictly positive — the
canonical "non-vanishing" condition for `pseudoMassFromParamsAtPair`
expressed in terms of the function `latticeMass` is defined against. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_pos_of_truncated2_mem
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  exact pseudoMass_pos hα hr htrunc

/-- **At `h = 0`, full sandwich `pseudoMass(c_max) ≤
pseudoMassFromParamsAtPair ≤ pseudoMass(c_min)`** under
`c_min ≤ truncated2 ≤ c_max` with all values in `Ioo 0 2`. Combines
`_at_h_zero_le_pseudoMass_of_truncated2_ge` and
`_at_h_zero_ge_pseudoMass_of_truncated2_le` (PR #1677) into a single
sandwich in terms of the typed `pseudoMass`. This is the canonical
sandwich form for §17.5 Lemma 17.5.2: a uniform-in-Λ exponential
decay bound on `truncated2Infinite` plus the Lipschitz capstone
(`pseudoMass_pow_succ_lipschitz`) on the typed `pseudoMass` would
combine into the sandwich `m⁻ ≤ m ≤ const · m⁻`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_sandwich_pseudoMass
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c_min c_max : ℝ}
    (hc_min : c_min ∈ Set.Ioo (0 : ℝ) 2)
    (hc_max : c_max ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2)
    (hge : c_min ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hle : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ c_max) :
    pseudoMass hα hr hc_max ≤
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ∧
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      pseudoMass hα hr hc_min :=
  ⟨pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_of_truncated2_le
      hα hr d Λ J β x z hc_max htrunc hle,
   pseudoMassFromParamsAtPair_at_h_zero_le_pseudoMass_of_truncated2_ge
      hα hr d Λ J β x z hc_min htrunc hge⟩

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` equals
the typed `pseudoMass(tanh(β·h)^2)`** when `0 < h` and `0 < β`
(ferromagnetic with strict positivity): `tanh(β·h) ∈ (0, 1)`, so
`tanh(β·h)^2 ∈ Ioo 0 1 ⊂ Ioo 0 2`, hence the totalisation collapses
to the typed `pseudoMass`. Combines `_at_J_zero_distinct_eq` (gives
`pseudoMassExt(tanh(β·h)^2)`) with `pseudoMassExt_of_mem`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ∃ hmem : Real.tanh (β * h) ^ 2 ∈ Set.Ioo (0 : ℝ) 2,
      pseudoMassFromParamsAtPair hα hr d Λ
          (⟨0, h, β⟩ : IsingParams ℝ) x z = pseudoMass hα hr hmem := by
  have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, hh.le, hβ⟩
  have habs : |Real.tanh (β * h)| < 1 := Real.abs_tanh_lt_one _
  have hlt_one : Real.tanh (β * h) < 1 := lt_of_abs_lt habs
  have hgt_neg_one : -1 < Real.tanh (β * h) := neg_lt_of_abs_lt habs
  have htanh_pos : 0 < Real.tanh (β * h) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ hh)) (Real.cosh_pos _)
  have hmem : Real.tanh (β * h) ^ 2 ∈ Set.Ioo (0 : ℝ) 2 := by
    refine ⟨by positivity, ?_⟩
    nlinarith
  refine ⟨hmem, ?_⟩
  rw [pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf hxz]
  exact pseudoMassExt_of_mem hα hr hmem

/-- **At `J = 0, h = 0` for ANY pair `(x, z)` (diag + distinct), the
bridge = 0**: combines `_diag_h_zero` (covers `x = z`, any J, β, h=0)
with `_at_J_zero_h_zero_eq_zero` (covers `x ≠ z` under `0 < β`).
At `J = h = 0`, the system is independent uniform spins for any β > 0,
so all 2-point correlations vanish identically. -/
theorem pseudoMassFromParamsAtPair_J_zero_h_zero_any_pair
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) x z = 0 := by
  by_cases hxz : x = z
  · subst hxz
    exact pseudoMassFromParamsAtPair_diag_h_zero hα hr d Λ 0 β x
  · exact pseudoMassFromParamsAtPair_at_J_zero_h_zero_eq_zero hα hr d Λ hβ hxz

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`ContinuousAt` in `β` for `β > 0`** (with `h > 0` fixed): combines
`_at_J_zero_distinct_eq` (the bridge equals `pseudoMassExt(tanh(β·h)^2)`)
with `pseudoMassExt_tanh_sq_continuousAt_pos` (PR #1685). Useful for
showing the J=0 reference slice is continuously parametrised by β. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousAt_beta_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ContinuousAt
      (fun b : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, h, b⟩ : IsingParams ℝ) x z) β := by
  have hf_at : ∀ b > 0, Ferromagnetic (⟨(0 : ℝ), h, b⟩ : IsingParams ℝ) :=
    fun b hb => ⟨le_refl 0, hh.le, hb⟩
  -- Use `pseudoMassFromParamsAtPair_at_J_zero_distinct_eq` to rewrite as
  -- `pseudoMassExt(tanh(b·h)^2)`. The rewrite holds for ferromagnetic params,
  -- which requires `b > 0`. Use `Filter.EventuallyEq` on a neighborhood of β.
  have hβ_nhd : ∀ᶠ b in nhds β, 0 < b := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨β / 2, by linarith, ?_⟩
    intros y hy
    rw [Real.dist_eq, abs_lt] at hy
    linarith
  have hEq : (fun b : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                              (⟨0, h, b⟩ : IsingParams ℝ) x z) =ᶠ[nhds β]
              (fun b : ℝ => pseudoMassExt hα hr (Real.tanh (b * h) ^ 2)) := by
    filter_upwards [hβ_nhd] with b hb
    exact pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ
            (hf_at b hb) hxz
  refine (ContinuousAt.congr ?_ hEq.symm)
  -- Continuity of `b ↦ pseudoMassExt(tanh(b·h)^2)` at β:
  -- Composition `(b ↦ b·h)` (continuous) then `pseudoMassExt(tanh(·)^2)`
  -- (continuous at β·h > 0 by PR #1685).
  have hβh_pos : 0 < β * h := mul_pos hβ hh
  have hmul : ContinuousAt (fun b : ℝ => b * h) β :=
    (continuous_id.mul continuous_const).continuousAt
  have houter : ContinuousAt
                  (fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) (β * h) :=
    pseudoMassExt_tanh_sq_continuousAt_pos hα hr hβh_pos
  change ContinuousAt
    ((fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) ∘ (fun b : ℝ => b * h)) β
  exact ContinuousAt.comp houter hmul

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`DifferentiableAt` in `β` for `β > 0`** (with `h > 0` fixed): same
proof structure as `_continuousAt_beta_pos` (PR #1686), substituting
`pseudoMassExt_tanh_sq_differentiableAt_pos` (PR #1685) for the
ContinuousAt version. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableAt_beta_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    DifferentiableAt ℝ
      (fun b : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, h, b⟩ : IsingParams ℝ) x z) β := by
  have hf_at : ∀ b > 0, Ferromagnetic (⟨(0 : ℝ), h, b⟩ : IsingParams ℝ) :=
    fun b hb => ⟨le_refl 0, hh.le, hb⟩
  have hβ_nhd : ∀ᶠ b in nhds β, 0 < b := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨β / 2, by linarith, ?_⟩
    intros y hy
    rw [Real.dist_eq, abs_lt] at hy
    linarith
  have hEq : (fun b : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                              (⟨0, h, b⟩ : IsingParams ℝ) x z) =ᶠ[nhds β]
              (fun b : ℝ => pseudoMassExt hα hr (Real.tanh (b * h) ^ 2)) := by
    filter_upwards [hβ_nhd] with b hb
    exact pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ
            (hf_at b hb) hxz
  have hdiff_alt : DifferentiableAt ℝ
                    (fun b : ℝ => pseudoMassExt hα hr (Real.tanh (b * h) ^ 2)) β := by
    have hβh_pos : 0 < β * h := mul_pos hβ hh
    have hmul : DifferentiableAt ℝ (fun b : ℝ => b * h) β :=
      (differentiable_id.mul (differentiable_const _)).differentiableAt
    have houter : DifferentiableAt ℝ
                    (fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) (β * h) :=
      pseudoMassExt_tanh_sq_differentiableAt_pos hα hr hβh_pos
    change DifferentiableAt ℝ
      ((fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) ∘ (fun b : ℝ => b * h)) β
    exact DifferentiableAt.comp β houter hmul
  exact hdiff_alt.congr_of_eventuallyEq hEq

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`DifferentiableAt` in `h` for `h > 0`** (with `β > 0` fixed):
h-direction analogue of `_differentiableAt_beta_pos`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableAt_h_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    DifferentiableAt ℝ
      (fun y : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, y, β⟩ : IsingParams ℝ) x z) h := by
  have hf_at : ∀ y > 0, Ferromagnetic (⟨(0 : ℝ), y, β⟩ : IsingParams ℝ) :=
    fun y hy => ⟨le_refl 0, hy.le, hβ⟩
  have hh_nhd : ∀ᶠ y in nhds h, 0 < y := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨h / 2, by linarith, ?_⟩
    intros y hy
    rw [Real.dist_eq, abs_lt] at hy
    linarith
  have hEq : (fun y : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                              (⟨0, y, β⟩ : IsingParams ℝ) x z) =ᶠ[nhds h]
              (fun y : ℝ => pseudoMassExt hα hr (Real.tanh (β * y) ^ 2)) := by
    filter_upwards [hh_nhd] with y hy
    exact pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ
            (hf_at y hy) hxz
  have hdiff_alt : DifferentiableAt ℝ
                    (fun y : ℝ => pseudoMassExt hα hr (Real.tanh (β * y) ^ 2)) h := by
    have hβh_pos : 0 < β * h := mul_pos hβ hh
    have hmul : DifferentiableAt ℝ (fun y : ℝ => β * y) h :=
      ((differentiable_const _).mul differentiable_id).differentiableAt
    have houter : DifferentiableAt ℝ
                    (fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) (β * h) :=
      pseudoMassExt_tanh_sq_differentiableAt_pos hα hr hβh_pos
    change DifferentiableAt ℝ
      ((fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) ∘ (fun y : ℝ => β * y)) h
    exact DifferentiableAt.comp h houter hmul
  exact hdiff_alt.congr_of_eventuallyEq hEq

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`ContinuousAt` in `h` for `h > 0`** (with `β > 0` fixed): h-direction
analogue of `_at_J_zero_distinct_continuousAt_beta_pos`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousAt_h_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ContinuousAt
      (fun y : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, y, β⟩ : IsingParams ℝ) x z) h := by
  have hf_at : ∀ y > 0, Ferromagnetic (⟨(0 : ℝ), y, β⟩ : IsingParams ℝ) :=
    fun y hy => ⟨le_refl 0, hy.le, hβ⟩
  have hh_nhd : ∀ᶠ y in nhds h, 0 < y := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨h / 2, by linarith, ?_⟩
    intros y hy
    rw [Real.dist_eq, abs_lt] at hy
    linarith
  have hEq : (fun y : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                              (⟨0, y, β⟩ : IsingParams ℝ) x z) =ᶠ[nhds h]
              (fun y : ℝ => pseudoMassExt hα hr (Real.tanh (β * y) ^ 2)) := by
    filter_upwards [hh_nhd] with y hy
    exact pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ
            (hf_at y hy) hxz
  refine (ContinuousAt.congr ?_ hEq.symm)
  have hβh_pos : 0 < β * h := mul_pos hβ hh
  have hmul : ContinuousAt (fun y : ℝ => β * y) h :=
    (continuous_const.mul continuous_id).continuousAt
  have houter : ContinuousAt
                  (fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) (β * h) :=
    pseudoMassExt_tanh_sq_continuousAt_pos hα hr hβh_pos
  change ContinuousAt
    ((fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) ∘ (fun y : ℝ => β * y)) h
  exact ContinuousAt.comp houter hmul

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`ContinuousOn (Ioi 0)` in `β`**: lift `_continuousAt_beta_pos` to a
`ContinuousOn` over the open positive real interval. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousOn_beta_Ioi
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 < h) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ContinuousOn
      (fun b : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, h, b⟩ : IsingParams ℝ) x z) (Set.Ioi 0) := by
  intro β hβ
  exact (pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousAt_beta_pos
            hα hr d Λ hh hβ hxz).continuousWithinAt

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`ContinuousOn (Ioi 0)` in `h`**: lift `_continuousAt_h_pos`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousOn_h_Ioi
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ContinuousOn
      (fun y : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, y, β⟩ : IsingParams ℝ) x z) (Set.Ioi 0) := by
  intro h hh
  exact (pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousAt_h_pos
            hα hr d Λ hh hβ hxz).continuousWithinAt

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`DifferentiableOn (Ioi 0)` in `β`**. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableOn_beta_Ioi
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 < h) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    DifferentiableOn ℝ
      (fun b : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, h, b⟩ : IsingParams ℝ) x z) (Set.Ioi 0) := by
  intro β hβ
  exact (pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableAt_beta_pos
            hα hr d Λ hh hβ hxz).differentiableWithinAt

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`DifferentiableOn (Ioi 0)` in `h`**. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableOn_h_Ioi
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    DifferentiableOn ℝ
      (fun y : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, y, β⟩ : IsingParams ℝ) x z) (Set.Ioi 0) := by
  intro h hh
  exact (pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableAt_h_pos
            hα hr d Λ hh hβ hxz).differentiableWithinAt

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
