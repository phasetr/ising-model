import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeContinuity
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.GlobalPseudoMassDist
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature.UpperBound
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature.PosAndAntitone
import Mathlib.Topology.Order.Monotone

/-!
# GJ §17.5 Theorem 17.5.1 — true-mass (`latticeMass`) structure on the high-temperature window

The continuity of the system **pseudo-mass** `m⁻ = globalPseudoMassDist` is formalized
(`globalPseudoMassDist_continuousOn_window`, the principal ingredient of GJ Theorem 17.5.1).  The
**true mass** `m = latticeMass` is a genuinely different object (`= sSup` of exponential decay
rates), and its continuity does **not** follow from `m⁻` continuity + the Lemma 17.5.2 sandwich
(`const ≠ 1`).  This file records what the true mass `m` *does* inherit on the high-temperature
window, honestly localizing the remaining gap:

* `latticeMass` is trapped between two **continuous** functions of `β`:
  `ofReal(m⁻(σ)) ≤ latticeMass(σ) ≤ ofReal(−log tanh(βJ))` (lower = `globalPseudoMassDist_le_lattice
  Mass`, continuous by the FV route; upper = `latticeMass_le_neg_log_tanh_betaJ`, continuous);
* `latticeMass` is finite and strictly positive on the window;
* `latticeMass` is **antitone** in `β`, hence continuous at all but **countably many** `β`
  (`AntitoneOn.countable_not_continuousWithinAt`).

The remaining gap to full GJ Theorem 17.5.1 (continuity of `m` everywhere on the window) is exactly
that the sandwich band `[m⁻, const·m⁻]` does not close (`const > 1`); closing it requires the §18
cluster-expansion analyticity (window real-analyticity of `m`) — see issue #4386.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 / Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Set

/-- **The true mass `latticeMass` is sandwiched by two continuous functions on the window** (GJ
§17.5): for `0<β₁≤β₂`, `β₂·J·2d<1/2`, `α≥d−1` (`d/2<α<d`), on `Icc β₁ β₂` the lower bound
`β ↦ ofReal(globalPseudoMassDist σ)` and the upper bound `β ↦ ofReal(−log tanh(βJ))` are both
`ContinuousOn`, and `lower β ≤ latticeMass σ ≤ upper β`.  Lower = `globalPseudoMassDist_le_lattice
Mass` (continuous via the FV route #4385); upper = `latticeMass_le_neg_log_tanh_betaJ` (continuous,
`tanh(βJ)>0`). -/
theorem latticeMass_sandwich_continuousOn_window {α d : ℕ} (hα : 1 ≤ α)
    (hd : 1 ≤ d) (hαd : d < 2 * α) (hαd2 : α < d) (hαd1 : d ≤ α + 1)
    {J β₁ β₂ : ℝ} (hJ : 0 < J) (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hβ₂_half : β₂ * J * (2 * d) < 1 / 2) :
    ContinuousOn (fun β => ENNReal.ofReal (globalPseudoMassDist hα (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ))) (Set.Icc β₁ β₂)
      ∧ ContinuousOn (fun β => ENNReal.ofReal (-Real.log (Real.tanh (β * J)))) (Set.Icc β₁ β₂)
      ∧ ∀ β ∈ Set.Icc β₁ β₂,
          ENNReal.ofReal (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
              ≤ latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            ∧ latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              ≤ ENNReal.ofReal (-Real.log (Real.tanh (β * J))) := by
  refine ⟨?_, ?_, ?_⟩
  · -- lower bound continuous: `ofReal ∘ globalPseudoMassDist`.
    exact ENNReal.continuous_ofReal.comp_continuousOn
      (globalPseudoMassDist_continuousOn_window hα hd hαd hαd2 hαd1 hJ hβ₁ hβ₁₂ hβ₂_half)
  · -- upper bound continuous: `ofReal ∘ (−log ∘ tanh ∘ (·*J))`.
    refine ENNReal.continuous_ofReal.comp_continuousOn ?_
    have htanh_cont : Continuous Real.tanh := by
      have hrw : Real.tanh = fun x => Real.sinh x / Real.cosh x := by
        ext x; exact Real.tanh_eq_sinh_div_cosh x
      rw [hrw]
      exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
    refine ContinuousOn.neg (ContinuousOn.log ?_ ?_)
    · exact (htanh_cont.comp (continuous_id.mul continuous_const)).continuousOn
    · intro β hβ
      have hβpos : 0 < β := lt_of_lt_of_le hβ₁ hβ.1
      have : 0 < Real.tanh (β * J) := by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβpos hJ)) (Real.cosh_pos _)
      exact ne_of_gt this
  · intro β hβ
    have hβpos : 0 < β := lt_of_lt_of_le hβ₁ hβ.1
    exact ⟨globalPseudoMassDist_le_latticeMass hα (cubicExhaustion d) hJ.le hβpos,
      latticeMass_le_neg_log_tanh_betaJ (by omega) hJ hβpos⟩

/-- **The true mass `latticeMass` is finite and strictly positive on the window** (GJ §17.5): for
the high-temperature window (`0<β₁≤β₂`, `β₂·J·2d<1/2`, `α≥d−1`), `0 < latticeMass σ < ⊤`.
Finiteness from the `−log tanh(βJ)` upper bound (`ofReal < ⊤`); positivity from `0 < m⁻(σ)` (the
strict-window lower bound #4360) via `ofReal(m⁻) ≤ latticeMass`. -/
theorem latticeMass_pos_lt_top_window {α d : ℕ} (hα : 1 ≤ α)
    (hd : 1 ≤ d) {J β₁ β₂ : ℝ} (hJ : 0 < J) (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hβ₂_half : β₂ * J * (2 * d) < 1 / 2)
    {β : ℝ} (hβmem : β ∈ Set.Icc β₁ β₂) :
    0 < latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ∧ latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) < ⊤ := by
  have hβpos : 0 < β := lt_of_lt_of_le hβ₁ hβmem.1
  refine ⟨?_, ?_⟩
  · -- positivity from `0 < m⁻` on the strict window.
    have hβ₂Jd_pos : 0 < β₂ * J * (2 * d) := by
      have hβ₂_pos : 0 < β₂ := lt_of_lt_of_le hβ₁ hβ₁₂
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
      positivity
    have hmmin_pos : 0 < globalPseudoMassDistRestrictedRate α d J β₂ :=
      globalPseudoMassDistRestrictedRate_pos (α := α) hβ₂Jd_pos hβ₂_half
    have hm_pos : 0 < globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) :=
      lt_of_lt_of_le hmmin_pos
        (globalPseudoMassDist_ge_restrictedRate_beta2 hα (by omega) hJ hβ₁ hβ₂_half β hβmem)
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hm_pos)
      (globalPseudoMassDist_le_latticeMass hα (cubicExhaustion d) hJ.le hβpos)
  · -- finiteness from the `−log tanh(βJ)` upper bound.
    exact lt_of_le_of_lt (latticeMass_le_neg_log_tanh_betaJ (by omega) hJ hβpos)
      ENNReal.ofReal_lt_top

/-- **The true mass `latticeMass` is continuous at all but countably many `β`** (GJ §17.5): the map
`β ↦ latticeMass σ` is antitone on `Ioi 0` (`latticeMass_antitone_beta`), hence — as a monotone-type
map into `ℝ≥0∞` — continuous within `Ioi 0` outside a countable set
(`AntitoneOn.countable_not_continuousWithinAt`).  This is the unconditional regularity the true mass
inherits; the remaining (countable) discontinuities are exactly the gap that the §18 analyticity
route (#4386) would close. -/
theorem latticeMass_countable_not_continuousWithinAt_Ioi {d : ℕ} {J : ℝ} (hJ : 0 < J) :
    Set.Countable {β ∈ Set.Ioi (0 : ℝ) |
      ¬ ContinuousWithinAt
          (fun β' => latticeMass d (cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ))
          (Set.Ioi 0) β} := by
  have hanti : AntitoneOn
      (fun β => latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) (Set.Ioi 0) := by
    intro β₁ hβ₁ β₂ _ hβ₁₂
    exact latticeMass_antitone_beta (cubicExhaustion d) hJ.le hβ₁ hβ₁₂
  exact hanti.countable_not_continuousWithinAt

end Ambient
end IsingModel
