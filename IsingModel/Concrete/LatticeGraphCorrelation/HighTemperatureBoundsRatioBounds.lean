import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete Λ-level Z ratio sandwich and ratio bound wrappers at h = 0

Narrow child module for the 10 §18.3-§18.4 concrete Λ-level
`partitionFunctionΛ_latticeGraph` `ratio_sandwich` / `ratio_bound`
wrappers on `latticeGraph d` at `h = 0` (with `J = 0` / `β = 0` /
`bundle` variants plus ferromagnetic counterparts). The 7
`triple_ratio_*` wrappers now live in
`HighTemperatureBoundsTripleRatio.lean` (narrowed in PR #1998); the
12 `log_partitionFunctionΛ_latticeGraph` / `freeEnergyΛ_latticeGraph`
ratio wrappers now live in `HighTemperatureBoundsRatioLogFe.lean`
(narrowed in PR #1999). Theorem names are unchanged from the former
`HighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Λ Z ratio sandwich at J=0**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) ∧
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ Z ratio sandwich at β=0**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ Z ratio sandwich bundle**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card)) ∧
    (Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card)) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ ferromagnetic Z ratio sandwich bundle**. -/
theorem
partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_sandwich_bundle_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    (Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card)) ∧
    (Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card)) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ

/-! ## Moved: ℤ^d Λ-direct Z ratio-bound wrappers

The six wrappers
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound`,
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_beta_zero`,
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_ferromagnetic`,
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_beta_zero_ferromagnetic`,
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_bundle`,
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic`
now live in `HighTemperatureBoundsRatioBoundsBound.lean`. -/

/-! ## Moved: ℤ^d Λ-direct log Z + freeEnergy ratio wrappers

The 12 ℤ^d Λ-direct `log_partitionFunction` and `freeEnergy`
ratio_sandwich / ratio_bound wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsRatioLogFe`.
The umbrella `HighTemperatureBounds.lean` re-imports
the new child so the import paths and theorem names remain
unchanged.
-/

/-! ## Moved: ℤ^d Λ-direct triple-ratio wrappers

The 7 ℤ^d Λ-direct `triple_ratio_sandwich_bundle` and
`triple_ratio_bound_bundle` wrappers (J = 0 / β = 0 trivial slices,
ferromagnetic variants) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsTripleRatio`.
The earlier import path is preserved by re-exporting the new child
from the umbrella module that aggregates both.
-/

end Ambient

end IsingModel
