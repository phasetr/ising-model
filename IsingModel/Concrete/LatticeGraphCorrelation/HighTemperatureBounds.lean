import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d fixed-volume high-temperature sandwich for `Z_Λ` and `f_Λ` at zero field

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ` and at the parameter
record `⟨J, 0, β⟩`, the high-temperature sandwich of the partition function between
`2 ^ |Λ| * cosh (β * J) ^ |E_Λ|` and `2 ^ (|Λ| + |E_Λ|) * cosh (β * J) ^ |E_Λ|`, and the
corresponding sandwich of the free-energy density between
`log 2 + (|E_Λ| / |Λ|) * log (cosh (β * J))` and
`log 2 + (|E_Λ| / |Λ|) * log (2 * cosh (β * J))`. Each rests on `0 ≤ β * J`; the free-energy
sandwich additionally needs `Λ` nonempty, which the partition-function sandwich does not.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Z high-temp sandwich (FV (3.45))**: under `0 ≤ β·J`,
`2^|Λ| · cosh^|E_Λ| ≤ Z_Λ ≤ 2^(|Λ|+|E_Λ|) · cosh^|E_Λ|`. ℤ^d wrapper. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
    ∧ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ (Λ.card +
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) *
          Real.cosh (β * J) ^
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d freeEnergy high-temp sandwich (FV (3.45))**: under `0 < |Λ|`
and `0 ≤ β·J`,
`log 2 + (|E_Λ|/|Λ|) · log cosh(βJ) ≤ f_Λ ≤ log 2 + (|E_Λ|/|Λ|) · log(2·cosh βJ)`.
ℤ^d wrapper. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
          Λ.card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
    ∧ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
            Λ.card * Real.log (2 * Real.cosh (β * J)) :=
  freeEnergyΛ_high_temp_h_zero_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ hne

end Ambient
end IsingModel
