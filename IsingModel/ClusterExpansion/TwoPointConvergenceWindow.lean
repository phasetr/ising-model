import IsingModel.ClusterExpansion.TwoPointDerivativeConvergenceRegion
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The real high-temperature window of the two-point convergence region

Toward eliminating the last declared axiom (§17.5 derivative-limit provider, Issue #4289 PR4b):
this file pins down a concrete real interval `window d J := Ioo 0 (artanh (R d) / J)` (with
`R d = twoPointHTActivityRadius (2d)`) whose `ofReal`-image lies in the complex convergence region
`U d J`, and which is a *subinterval* of the formal high-temperature interval `Ioo 0 (1/(J·2d))`.
On this window the locally-uniform two-point β-derivative convergence of PR4a
(`derivativeLimit_on_real_subinterval`) holds **axiom-free**, giving a concrete derivative-limit
provider on the genuine convergence sub-window.

The two structural facts are:

* `ofReal_window_mem_U` — every `β ∈ window d J` embeds into `U d J` (so the window feeds PR4a);
* `window_subset_highTemp` — `window d J ⊆ Ioo 0 (1/(J·2d))` (the numeric crux
  `artanh (R d) ≤ 1/(2d)`, so the §17.5 sharp-HLS capstone hypotheses scoped to the window imply
  the original high-temperature ones).

**Reference:** Glimm–Jaffe, 2nd ed., §17.5 pp. 311–312, §18.6–18.7. -/

namespace IsingModel
namespace ConvergenceRegion

open Filter Topology Set

variable (d : ℕ) (J : ℝ)

/-- The activity radius is `< 1` (it is below `1/64` already from the first `min` branch). -/
theorem R_lt_one : R d < 1 := by
  have hle : R d ≤ 1 / (64 * ((((2 * d : ℕ) : ℝ) ^ 2 + 1) * Real.exp 1)) := by
    unfold R twoPointHTActivityRadius; exact min_le_left _ _
  have hpos : (0 : ℝ) < 64 * ((((2 * d : ℕ) : ℝ) ^ 2 + 1) * Real.exp 1) := by positivity
  have hden : (1 : ℝ) < 64 * ((((2 * d : ℕ) : ℝ) ^ 2 + 1) * Real.exp 1) := by
    have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hsq : (0 : ℝ) ≤ ((2 * d : ℕ) : ℝ) ^ 2 := sq_nonneg _
    nlinarith [hsq, he]
  have hlt : 1 / (64 * ((((2 * d : ℕ) : ℝ) ^ 2 + 1) * Real.exp 1)) < 1 := by
    rw [div_lt_one hpos]; exact hden
  linarith

/-- The real high-temperature window: the interval `(0, artanh(R d)/J)`.  Its `ofReal`-image lies in
the complex convergence region `U d J` and it is a subinterval of `Ioo 0 (1/(J·2d))`. -/
noncomputable def window : Set ℝ := Set.Ioo (0 : ℝ) (Real.artanh (R d) / J)

/-- **Window membership embeds into `U`.**  For `0 < J`, every real `β` in the window
`(0, artanh(R d)/J)` embeds as `(β : ℂ) ∈ U d J`: the activity `tanh(βJ)` stays strictly below the
radius `R d` because `βJ < artanh(R d)` and `artanh` inverts `tanh`. -/
theorem ofReal_window_mem_U {β : ℝ} (hJ : 0 < J) (hβ : β ∈ window d J) :
    (β : ℂ) ∈ U d J := by
  obtain ⟨hβ0, hβlt⟩ := hβ
  -- `βJ < artanh (R d)`.
  have hβJ : β * J < Real.artanh (R d) := by
    rw [lt_div_iff₀ hJ] at hβlt; linarith [hβlt]
  -- The activity radius lies in `(-1, 1)` so `artanh ∘ tanh = id` is usable.
  have hRpos : 0 < R d := twoPointHTActivityRadius_pos (2 * d)
  have hRlt1 : R d < 1 := R_lt_one d
  -- `tanh (βJ) < R d`, via strict monotonicity of `artanh` and `artanh (tanh x) = x`.
  have htanh_lt : Real.tanh (β * J) < R d := by
    have hlt : Real.artanh (Real.tanh (β * J)) < Real.artanh (R d) := by
      rw [Real.artanh_tanh]; exact hβJ
    have h1 : Real.tanh (β * J) ∈ Set.Ioo (-1 : ℝ) 1 :=
      ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩
    have h2 : R d ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hRlt1⟩
    exact (Real.artanh_lt_artanh_iff h1 h2).mp hlt
  -- `0 < tanh (βJ)` (since `βJ > 0`), hence `‖Complex.tanh (βJ)‖ = tanh (βJ) < R d`.
  have hβJpos : 0 < β * J := mul_pos hβ0 hJ
  have htanh_pos : 0 < Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hβJpos) (Real.cosh_pos _)
  refine ofReal_mem_U d J hβ0.le ?_ hJ.le
  have hcast : (β : ℂ) * (J : ℂ) = ((β * J : ℝ) : ℂ) := by rw [Complex.ofReal_mul]
  rw [hcast, ← Complex.ofReal_tanh, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos htanh_pos]
  exact htanh_lt

/-- The numeric crux `artanh (R d) ≤ 1/(2d)` (for `d ≥ 1`): the activity radius is so small that
`R d ≤ tanh(1/(2d))`, hence `artanh (R d) ≤ artanh(tanh(1/(2d))) = 1/(2d)`. -/
private theorem artanh_R_le_inv (hd : 1 ≤ d) :
    Real.artanh (R d) ≤ 1 / (2 * (d : ℝ)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set s : ℝ := 1 / (2 * (d : ℝ)) with hs
  have hspos : 0 < s := by rw [hs]; positivity
  have hs_le_one : s ≤ 1 := by
    rw [hs, div_le_one (by positivity)]; nlinarith [hd1]
  -- `cosh s ≤ 2` (via `cosh s ≤ cosh 1` and `cosh 1 < 2`).
  have hcosh1 : Real.cosh 1 ≤ 2 := by
    rw [Real.cosh_eq]
    have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h2 : Real.exp (-1 : ℝ) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_le_exp.mpr (by norm_num)
    have h3 : (0 : ℝ) < Real.exp (-1 : ℝ) := Real.exp_pos _
    linarith
  have hcosh_s : Real.cosh s ≤ 2 := by
    have hle : Real.cosh s ≤ Real.cosh 1 := by
      rw [Real.cosh_le_cosh, abs_of_pos hspos, abs_of_pos (by norm_num : (0:ℝ) < 1)]
      exact hs_le_one
    linarith
  -- `s/2 ≤ tanh s`.
  have hcosh_pos : 0 < Real.cosh s := Real.cosh_pos _
  have hsinh : s ≤ Real.sinh s := Real.self_le_sinh_iff.mpr hspos.le
  have htanh_ge : s / 2 ≤ Real.tanh s := by
    rw [Real.tanh_eq_sinh_div_cosh, le_div_iff₀ hcosh_pos]
    have hmul : s / 2 * Real.cosh s ≤ s / 2 * 2 :=
      mul_le_mul_of_nonneg_left hcosh_s (by positivity)
    nlinarith [hsinh, hmul]
  -- `R d ≤ 1/(4d) = s/2`.
  have hRle1 : R d ≤ 1 / (64 * ((((2 * d : ℕ) : ℝ) ^ 2 + 1) * Real.exp 1)) := by
    unfold R twoPointHTActivityRadius; exact min_le_left _ _
  have hcast : ((2 * d : ℕ) : ℝ) = 2 * (d : ℝ) := by push_cast; ring
  rw [hcast] at hRle1
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hquarter : (1 : ℝ) / (64 * (((2 * (d : ℝ)) ^ 2 + 1) * Real.exp 1)) ≤ s / 2 := by
    have hs2 : s / 2 = 1 / (4 * (d : ℝ)) := by rw [hs]; field_simp; ring
    rw [hs2]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [he, hdpos, sq_nonneg ((d : ℝ)), hd1]
  have hRle : R d ≤ s / 2 := le_trans hRle1 hquarter
  -- Combine: `R d ≤ s/2 ≤ tanh s`, then apply `artanh` monotone + `artanh ∘ tanh`.
  have hRpos : 0 < R d := twoPointHTActivityRadius_pos (2 * d)
  have hkey : R d ≤ Real.tanh s := le_trans hRle htanh_ge
  have hmono : Real.artanh (R d) ≤ Real.artanh (Real.tanh s) :=
    Real.artanh_le_artanh (by linarith) (Real.tanh_lt_one _) hkey
  rwa [Real.artanh_tanh] at hmono

/-- **The window is a subinterval of the formal high-temperature interval.**  For `0 < J` and
`d ≥ 1`, `window d J ⊆ Ioo 0 (1/(J·2d))`.  This lets the §17.5 sharp-HLS capstone hypotheses scoped
to the window imply the original high-temperature ones. -/
theorem window_subset_highTemp (hJ : 0 < J) (hd : 1 ≤ d) :
    window d J ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) := by
  rintro β ⟨hβ0, hβlt⟩
  refine ⟨hβ0, ?_⟩
  have hartanh : Real.artanh (R d) ≤ 1 / (2 * (d : ℝ)) := artanh_R_le_inv d hd
  have hub : Real.artanh (R d) / J ≤ 1 / (J * ↑(2 * d)) := by
    rw [div_le_div_iff₀ hJ (by positivity)]
    have hcast : ((2 * d : ℕ) : ℝ) = 2 * (d : ℝ) := by push_cast; ring
    rw [hcast]
    rw [le_div_iff₀ (by positivity)] at hartanh
    nlinarith [hartanh, hJ.le]
  linarith [hβlt, hub]

/-- **Axiom-free derivative-limit provider on the convergence window** (GJ §17.5 / §18.6–18.7,
Issue #4289 PR4b).  Specializing PR4a's `derivativeLimit_on_real_subinterval` to the window
`window d J` (whose `ofReal`-image lies in `U d J` by `ofReal_window_mem_U`) gives the
locally-uniform convergence of the finite-volume two-point β-derivatives on the window — the genuine
sub-window form of the §17.5 derivative-limit provider, proven with **no axiom**. -/
theorem derivativeLimit_on_window
    (Λ : Ambient.Exhaustion (Fin d → ℤ)) (hJ : 0 < J)
    {i j : Fin d → ℤ} (hij : i ≠ j) :
    ∃ g' : ℝ → ℝ,
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n) β)
        g' Filter.atTop (window d J) := by
  -- The window's upper endpoint is positive (`artanh (R d) > 0`, `J > 0`).
  have hRpos : 0 < R d := twoPointHTActivityRadius_pos (2 * d)
  have hRlt1 : R d < 1 := R_lt_one d
  have hartanh_pos : 0 < Real.artanh (R d) := Real.artanh_pos ⟨hRpos, hRlt1⟩
  have hc : 0 < Real.artanh (R d) / J := div_pos hartanh_pos hJ
  exact derivativeLimit_on_real_subinterval d Λ J hJ.le hij hc
    (fun β hβ => ofReal_window_mem_U d J hJ hβ)

end ConvergenceRegion
end IsingModel
