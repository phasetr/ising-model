import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrict
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBounds
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeFreeEnergyBoundOnly
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeLogBound
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeNonempty

/-!
# Ambient alongExhaustion log Z / freeEnergy ratio sandwich / bound wrappers at h = 0

Narrow child module for 12 §18.3-§18.4 ambient alongExhaustion
`log_partitionFunction` and `freeEnergy` ratio_sandwich /
ratio_bound (+ deviation_pos / pow_two_lt) wrappers at h = 0 (with
J = 0 / β = 0 trivial slices and ferromagnetic variants). Theorem
names are unchanged from the former
`HighTemperatureBoundsRatioBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

theorem freeEnergyAlongExhaustion_high_temp_h_zero_ratio_sandwich_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) / (Λ.volume n).card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) / (Λ.volume n).card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) := by
  change (_ ≤ freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
      - freeEnergyΛ G (Λ.volume n) (⟨0, 0, β⟩ : IsingParams ℝ) ∧ _) ∧
      (_ ≤ freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ G (Λ.volume n) (⟨J, 0, 0⟩ : IsingParams ℝ) ∧ _)
  exact freeEnergyΛ_high_temp_h_zero_ratio_sandwich_bundle
    G (Λ.volume n) J β hβJ hne

/-- **Along-ex ferromagnetic f ratio sandwich bundle at stage `n`**. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_ratio_sandwich_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) / (Λ.volume n).card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) / (Λ.volume n).card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) :=
  freeEnergyAlongExhaustion_high_temp_h_zero_ratio_sandwich_bundle
    G Λ J β (mul_nonneg hβ.le hJ) n hne

/-! ## Moved: log Z `ratio_sandwich_bundle` wrapper; ## Removed: log Z `ratio_bound` wrappers

The general ambient alongExhaustion
`log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle`
wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeLogBound`;
the earlier import path is preserved by re-exporting that child from the
umbrellas `HighTemperatureBounds.lean` / this parent module (which
re-imports the child below).

The other five log Z wrappers — the ferromagnetic `ratio_sandwich_bundle`
variant and the four `ratio_bound` variants (`J = 0`, `β = 0`,
`ratio_bound_bundle`, and `ratio_bound_bundle_ferromagnetic`) — were
removed as unused pass-through wrappers.
-/

/-! ## Moved: ratio-LogFe `_of_nonempty` wrappers

The three `*AlongExhaustion_high_temp_*_of_nonempty` wrappers
(`freeEnergyAlongExhaustion_*_deviation_bound_exp_of_nonempty`,
`freeEnergyAlongExhaustion_*_deviation_pos_of_nonempty`,
`partitionFunctionAlongExhaustion_*_pow_two_lt_of_nonempty`) now live
in `HighTemperatureBoundsRatioLogFeNonempty.lean`. They are re-imported
here so downstream consumers continue to see the symbols. -/



/-! ## Moved: freeEnergy `ratio_bound` non-bundle wrappers

The four ambient alongExhaustion `freeEnergyAlongExhaustion`
`ratio_bound` non-bundle slice variants (`J = 0` / `β = 0` and their
ferromagnetic counterparts) live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeFreeEnergyBoundOnly`.
The two `ratio_bound_bundle` wrappers (general and ferromagnetic) were
removed as unused conjunction bundles; downstream consumers reach the
non-bundle slices by importing that child directly.
-/

end Ambient

end IsingModel
