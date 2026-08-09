import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpper

/-!
# ℤ^d high-temperature lower and upper bounds for `Z` and their consistency (§18.3)

Instantiates at `IsingModel.latticeGraph d`, at the parameter record `⟨J, 0, β⟩`, the upper
bound `2 ^ (|Λ| + |E_Λ|) * cosh (β * J) ^ |E_Λ|` on the partition function, on a fixed finite
volume and at a stage `n` of an `Ambient.Exhaustion` of `Fin d → ℤ`, the matching lower bound
`2 ^ |Λ| * cosh (β * J) ^ |E_Λ|` on a fixed volume, and the consistency statements comparing
the bounding expressions directly, for the partition function and for the free-energy density.
The comparison of the partition-function bounds holds with no condition on `J` or `β`; every
other statement here assumes `0 ≤ β * J`, and none assumes `Λ` nonempty.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Z high-temperature upper bound (GJ §18.3 / FV (3.45))**:
under `0 ≤ β·J`,
`Z_Λ(⟨J, 0, β⟩) ≤ 2^(|Λ|+|E_Λ|) · cosh(βJ)^|E_Λ|`. ℤ^d wrapper of
`partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_upper_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ (Λ.card +
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) *
        Real.cosh (β * J) ^
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d along-exhaustion Z high-temperature upper bound**:
under `0 ≤ β·J`, at every stage `n`,
`Z_n ≤ 2^(|Λ_n|+|E_n|) · cosh(βJ)^|E_n|`. ℤ^d wrapper. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_upper_bound
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ ((Λ.volume n).card +
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) *
        Real.cosh (β * J) ^
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d Z bounds consistency**: lower ≤ upper. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_h_zero_lower_le_upper
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ (2 : ℝ) ^ (Λ.card +
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) *
        Real.cosh (β * J) ^
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  partitionFunctionΛ_high_temp_h_zero_lower_le_upper
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d freeEnergy bounds consistency**: lower ≤ upper. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_lower_le_upper
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
          Λ.card * Real.log (Real.cosh (β * J))
      ≤ Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
            Λ.card * Real.log (2 * Real.cosh (β * J)) :=
  freeEnergyΛ_high_temp_h_zero_lower_le_upper
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d high-temperature partition function lower bound (GJ §18.3 / FV (3.45))**:
under `0 ≤ β * J`,
`Z_Λ(⟨J, 0, β⟩) ≥ 2^|Λ| · (cosh(βJ))^|E_Λ|`.
ℤ^d wrapper of `partitionFunctionΛ_high_temp_expansion_h_zero_lower_bound`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_lower_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_lower_bound
    (IsingModel.latticeGraph d) Λ J β hβJ

end Ambient

end IsingModel
