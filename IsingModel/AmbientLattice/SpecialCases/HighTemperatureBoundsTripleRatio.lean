import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBounds
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFe

/-!
# Ambient alongExhaustion triple-ratio (Z + log Z + f) sandwich / bound wrappers at h = 0

Narrow child module for 7 §18.3-§18.4 ambient alongExhaustion
`triple_ratio_sandwich_bundle` and `triple_ratio_bound_bundle`
wrappers (J = 0 trivial slice, β = 0 specialisation, ferromagnetic
variants). The theorem names are unchanged from the former
`HighTemperatureBoundsRatioBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex triple (Z + log Z + f) ratio sandwich bundle at J=0, stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    (Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
        ≤ partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n /
            partitionFunctionAlongExhaustion G Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
      partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n /
          partitionFunctionAlongExhaustion G Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n
          ≤ Real.exp (β * J *
              (inducedGraph G (Λ.volume n)).edgeFinset.card)) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion G Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion G Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n)
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
        (Λ.volume n).card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) :=
  ⟨(partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle
      G Λ J β hβJ n).1,
   (log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle
      G Λ J β hβJ n).1,
   (freeEnergyAlongExhaustion_high_temp_h_zero_ratio_sandwich_bundle
      G Λ J β hβJ n hne).1⟩

/-- **Along-ex triple ratio sandwich bundle at β=0, stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    (Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
        ≤ partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n /
            partitionFunctionAlongExhaustion G Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
      partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n /
          partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n
          ≤ Real.exp (β * J *
              (inducedGraph G (Λ.volume n)).edgeFinset.card)) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion G Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion G Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n)
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    (((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
        (Λ.volume n).card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
          ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) :=
  ⟨(partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle
      G Λ J β hβJ n).2,
   (log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle
      G Λ J β hβJ n).2,
   (freeEnergyAlongExhaustion_high_temp_h_zero_ratio_sandwich_bundle
      G Λ J β hβJ n hne).2⟩

/-! ## Moved: 2 ferromagnetic triple ratio sandwich bundle wrappers

The two ferromagnetic `triple_ratio_sandwich_bundle*_ferromagnetic`
wrappers
(`partitionFunctionAlongExhaustion_h_zero_triple_ratio_sandwich_bundle_beta_zero_ferromagnetic`,
`partitionFunctionAlongExhaustion_h_zero_triple_ratio_sandwich_bundle_ferromagnetic`)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsTripleRatioFerro`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-! ## Moved: triple_ratio_bound_bundle wrappers

The three `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_bound_bundle*`
wrappers (general, `_beta_zero`, ferromagnetic) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsTripleRatioBoundBundle`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient

end IsingModel
