import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete f/Z/log Z deviation / continuity wrappers at h = 0

Narrow child module for the §18.3-§18.4 concrete deviation_bound /
continuity_bundle / deviation_sandwich / relative_sandwich / deviation_pos /
pow_two_lt / strict_deviation_bundle wrappers on `latticeGraph d` at
`h = 0`. 18 theorems for `freeEnergyΛ_latticeGraph`,
`partitionFunctionΛ_latticeGraph`, and
`log_partitionFunctionΛ_latticeGraph`, with their ferromagnetic variants.
The theorem names are unchanged from the former `HighTemperatureBounds`
declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff


/-! ## Moved: ℤ^d HT Λ-layer deviation_bound + continuity wrappers

The 4 ℤ^d Λ-layer `freeEnergyΛ_latticeGraph_high_temp_h_zero_*`
wrappers (`deviation_bound_exp`, `deviation_bound_exp_ferromagnetic`,
`continuity_bundle`, `continuity_bundle_ferromagnetic`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsDeviationContinuity`.
The earlier import path is preserved by re-importing the new child.
-/

/-- **ℤ^d Λ f deviation sandwich**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_deviation_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    0 ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2 ∧
    freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  freeEnergyΛ_high_temp_h_zero_deviation_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d Λ ferromagnetic f deviation sandwich**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_deviation_sandwich_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    0 ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2 ∧
    freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  freeEnergyΛ_high_temp_h_zero_deviation_sandwich_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ hne

/-- **ℤ^d Λ log Z deviation sandwich**. -/
theorem log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_deviation_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    0 ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)) - (Λ.card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)) - (Λ.card : ℝ) * Real.log 2
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ ferromagnetic log Z deviation sandwich**. -/
theorem
log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_deviation_sandwich_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    0 ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)) - (Λ.card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)) - (Λ.card : ℝ) * Real.log 2
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_sandwich_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ

/-! ## Moved: Λ-direct partitionFunctionΛ relative-sandwich wrappers

The two Λ-direct
`partitionFunctionΛ_*_relative_sandwich` wrappers (direct +
`_ferromagnetic`) now live in
`HighTemperatureBoundsDeviationRelative.lean`. -/



/-! ## Moved: ℤ^d HT Λ-layer strict-deviation wrappers

The 8 ℤ^d Λ-layer strict-deviation HT wrappers
(`freeEnergyΛ_latticeGraph_high_temp_h_zero_deviation_pos`,
`_ferromagnetic`,
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_pow_two_lt`,
`_ferromagnetic`,
`log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_deviation_pos`,
`_ferromagnetic`,
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_strict_deviation_bundle`,
`_ferromagnetic`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsDeviationStrict`.
The earlier import path is preserved by re-importing the new child.
-/

end Ambient

end IsingModel
