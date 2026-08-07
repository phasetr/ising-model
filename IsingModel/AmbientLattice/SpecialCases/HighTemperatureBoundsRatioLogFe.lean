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
# Ambient alongExhaustion free-energy ratio-sandwich bundles at h = 0

Bundles the GJ §18.3–§18.4 two-sided estimate for the zero-field free energy along an
exhaustion, in general and ferromagnetic form, so the §18.7 argument can quote a single
conjunction rather than reassembling the two bounds.
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

end Ambient

end IsingModel
