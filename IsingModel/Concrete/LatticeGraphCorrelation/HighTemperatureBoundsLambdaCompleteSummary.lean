import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d fixed-volume complete-summary bundles at zero field

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ` and at the parameter
record `⟨J, 0, β⟩`, bundles collecting, for the partition function and for the free-energy
density, their high-temperature lower and upper bounds in `cosh (β * J)` together with the
values taken at `⟨0, 0, β⟩` and at `⟨J, 0, 0⟩`. Each assumes `0 ≤ β * J`; the free-energy
bundle additionally needs `Λ` nonempty, which the partition-function bundle does not.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ Z complete-summary bundle at h = 0**: under `0 ≤ β·J`,
single statement bundling Λ Z bounds and trivial-slice values. ℤ^d
wrapper of `partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_complete_summary
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
        ≤ (2 : ℝ) ^ (Λ.card +
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) *
            Real.cosh (β * J) ^
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card ∧
      partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ) = (2 : ℝ) ^ Λ.card ∧
      partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ) = (2 : ℝ) ^ Λ.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ freeEnergy complete-summary bundle at h = 0**: under
`0 < |Λ|` and `0 ≤ β·J`, single statement bundling Λ-level lower /
upper bounds and trivial-slice values at `J = 0` / `β = 0` (both =
`log 2`). ℤ^d wrapper of
`freeEnergyΛ_high_temp_h_zero_complete_summary`. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_complete_summary
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
          Λ.card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
        ≤ Real.log 2 +
            ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
              Λ.card * Real.log (2 * Real.cosh (β * J)) ∧
      freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
      freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  freeEnergyΛ_high_temp_h_zero_complete_summary
    (IsingModel.latticeGraph d) Λ J β hβJ hne


end Ambient

end IsingModel
