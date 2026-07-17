import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete Λ-direct partitionFunctionΛ relative-sandwich wrappers

Narrow child module for 2 ℤ^d Λ-direct
`partitionFunctionΛ_*_relative_sandwich` wrappers extracted from
`HighTemperatureBoundsDeviation.lean`:

* `partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_relative_sandwich`,
* `partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_relative_sandwich_ferromagnetic`.

Each result is a thin pass-through of the corresponding ambient
`partitionFunctionΛ_high_temp_expansion_h_zero_relative_sandwich*`
lemma at `G := IsingModel.latticeGraph d`. The theorem names are
unchanged from the former `HighTemperatureBoundsDeviation`
declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d Λ Z relative-deviation sandwich**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_relative_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) / (2 : ℝ) ^ Λ.card ∧
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) / (2 : ℝ) ^ Λ.card
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_relative_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ ferromagnetic Z relative-deviation sandwich**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_relative_sandwich_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) / (2 : ℝ) ^ Λ.card ∧
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) / (2 : ℝ) ^ Λ.card
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_relative_sandwich_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ

end Ambient

end IsingModel
