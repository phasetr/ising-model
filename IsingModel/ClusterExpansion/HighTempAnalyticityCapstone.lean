import IsingModel.ClusterExpansion.HighTempKoteckyPreissRegularity
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Existence of a high-temperature analyticity threshold (GJ §18.6 — no phase transition)

The §18.6 free-energy analyticity results of `HighTempKoteckyPreiss.lean` /
`HighTempKoteckyPreissRegularity.lean` are stated on an interval `(0, artanh T / J)` whose existence
requires choosing radii `R, T` satisfying the Kotecký–Preiss threshold `(2d)^2 e\{R,T\} < 1/6`. This
file *exhibits* an explicit such radius and packages the results as clean **existential**
statements: for every dimension `d` and coupling `J > 0` there is a positive threshold `β₀` below
which the infinite-volume ℤ^d Ising free energy (and its temperature derivatives) is real-analytic —
the quantitative ``no phase transition at high temperature'' statement, free of the auxiliary
`R, T, hkp, hρ` machinery.

The explicit radius is `kpRadius d = 1 / (7·((2d)^2 + 1)·e)`: its denominator is positive for every
`d` (no `d = 0` division issue), and
\[
  (2d)^2\,e\cdot\texttt{kpRadius}\,d = \frac{(2d)^2}{7\,((2d)^2+1)} < \tfrac17 < \tfrac16,
  \qquad \texttt{kpRadius}\,d < 1,
\]
so it meets the high-temperature threshold of `kp_tail_conditions_of_lt`.

* `kpRadius`, `kpRadius_pos`, `kpRadius_lt_one`, `kpRadius_threshold` — the explicit radius and its
  defining estimates.
* `exists_high_temp_freeEnergyInfinite_analyticOnNhd` — `∃ β₀ > 0`, free-energy analyticity on
  `(0, β₀)` in the inverse temperature.
* `exists_high_temp_specificHeat_analyticOnNhd` — `∃ β₀ > 0`, specific-heat (`∂_β² f`) analyticity:
  no singularity, hence no phase transition, on `(0, β₀)`.
* `exists_high_temp_freeEnergyInfinite_analyticOnNhd_J` — `∃ J₀ > 0`, analyticity in the coupling on
  `(0, J₀)`.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.6, pp. 335–340.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §5.4 (Theorem 5.4, Kotecký–Preiss).
-/

namespace IsingModel

open Finset Filter Topology Ambient Real

/-- **Explicit high-temperature Kotecký–Preiss radius** `kpRadius d = 1/(7·((2d)²+1)·e)`. The `+1`
keeps the denominator positive for every `d` (including `d = 0`). -/
noncomputable def kpRadius (d : ℕ) : ℝ :=
  1 / (7 * (((2 * d : ℕ) : ℝ) ^ 2 + 1) * Real.exp 1)

/-- The explicit Kotecký–Preiss radius is positive. -/
theorem kpRadius_pos (d : ℕ) : 0 < kpRadius d := by
  unfold kpRadius; positivity

/-- The explicit Kotecký–Preiss radius is `< 1`. -/
theorem kpRadius_lt_one (d : ℕ) : kpRadius d < 1 := by
  unfold kpRadius
  rw [div_lt_one (by positivity)]
  nlinarith [Real.add_one_le_exp (1 : ℝ), sq_nonneg ((2 * d : ℕ) : ℝ), Real.exp_pos 1]

/-- The explicit radius meets the high-temperature threshold `(2d)² e · kpRadius d < 1/6`, since
`(2d)² e · kpRadius d = (2d)²/(7((2d)²+1)) < 1/7 < 1/6`. -/
theorem kpRadius_threshold (d : ℕ) :
    ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * kpRadius d) < 1 / 6 := by
  unfold kpRadius
  rw [show ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * (1 / (7 * (((2 * d : ℕ) : ℝ) ^ 2 + 1)
        * Real.exp 1))) = ((2 * d : ℕ) : ℝ) ^ 2 / (7 * (((2 * d : ℕ) : ℝ) ^ 2 + 1)) from by
      field_simp]
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [sq_nonneg ((2 * d : ℕ) : ℝ)]

/-- **High-temperature analyticity threshold for the free energy** (GJ §18.6, no phase transition):
for every dimension `d` and coupling `J > 0`, there is `β₀ > 0` such that the infinite-volume ℤ^d
Ising free energy at zero field is real-analytic in the inverse temperature on `(0, β₀)`. -/
theorem exists_high_temp_freeEnergyInfinite_analyticOnNhd (d : ℕ) {J : ℝ} (hJ : 0 < J) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ AnalyticOnNhd ℝ (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ)) (Set.Ioo 0 β₀) := by
  refine ⟨Real.artanh (kpRadius d) / J, ?_, ?_⟩
  · exact div_pos (Real.artanh_pos ⟨kpRadius_pos d, kpRadius_lt_one d⟩) hJ
  · exact freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_high_temp_of_activity
      d hJ (kpRadius_pos d) (kpRadius_pos d) le_rfl (kpRadius_lt_one d)
      (kpRadius_threshold d) (kpRadius_threshold d)

/-- **High-temperature analyticity of the specific heat** (GJ §18.6, no phase transition): for every
`d` and `J > 0`, there is `β₀ > 0` such that the specific heat `∂_β² f` of the infinite-volume ℤ^d
Ising free energy is real-analytic on `(0, β₀)` — no singularity, no phase transition there. -/
theorem exists_high_temp_specificHeat_analyticOnNhd (d : ℕ) {J : ℝ} (hJ : 0 < J) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ AnalyticOnNhd ℝ (deriv (deriv (fun β' : ℝ =>
        Ambient.freeEnergyInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β'⟩ : IsingParams ℝ)))) (Set.Ioo 0 β₀) := by
  refine ⟨Real.artanh (kpRadius d) / J, ?_, ?_⟩
  · exact div_pos (Real.artanh_pos ⟨kpRadius_pos d, kpRadius_lt_one d⟩) hJ
  · exact freeEnergyInfinite_latticeGraph_cubicExhaustion_specificHeat_high_temp_of_activity
      d hJ (kpRadius_pos d) (kpRadius_pos d) le_rfl (kpRadius_lt_one d)
      (kpRadius_threshold d) (kpRadius_threshold d)

/-- **High-temperature analyticity threshold in the coupling** (GJ §18.6): for every `d` and inverse
temperature `β > 0`, there is `J₀ > 0` such that the infinite-volume ℤ^d Ising free energy at zero
field is real-analytic in the coupling on `(0, J₀)`. -/
theorem exists_high_temp_freeEnergyInfinite_analyticOnNhd_J (d : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ J₀ : ℝ, 0 < J₀ ∧ AnalyticOnNhd ℝ (fun J' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J', 0, β⟩ : IsingParams ℝ)) (Set.Ioo 0 J₀) := by
  refine ⟨Real.artanh (kpRadius d) / β, ?_, ?_⟩
  · exact div_pos (Real.artanh_pos ⟨kpRadius_pos d, kpRadius_lt_one d⟩) hβ
  · exact freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_J_high_temp_of_activity
      d hβ (kpRadius_pos d) (kpRadius_pos d) le_rfl (kpRadius_lt_one d)
      (kpRadius_threshold d) (kpRadius_threshold d)

end IsingModel
