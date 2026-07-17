import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete sharper-exp Z/f/log Z high-temperature bounds at h = 0

Narrow child module for the §18.3-§18.4 concrete sharper-exp upper-bound /
sandwich / complete-summary wrappers on `latticeGraph d` at `h = 0`. 17
theorems covering `partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_*_exp`,
`freeEnergyΛ_latticeGraph_high_temp_h_zero_*_exp`, and
`log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_*_exp`
families (upper-bound, sandwich, complete-summary), each with their
ferromagnetic variants. The theorem names are unchanged from the former
`HighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Λ sharper Z upper bound**: under `0 ≤ β·J`,
`Z_Λ ≤ 2^|Λ| · exp(β·J·|E_Λ|)`. ℤ^d wrapper. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_upper_bound_exp
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ Λ.card *
          Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound_exp
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ sharper freeEnergy upper bound**: under `0 < |Λ|` and
`0 ≤ β·J`, `f_Λ ≤ log 2 + β·J·|E_Λ|/|Λ|`. ℤ^d wrapper. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_upper_bound_exp
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 +
          β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
              Λ.card :=
  freeEnergyΛ_high_temp_h_zero_upper_bound_exp
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d Λ sharper log Z upper bound**: under `0 ≤ β·J`,
`log Z_Λ ≤ |Λ|·log 2 + β·J·|E_Λ|`. ℤ^d wrapper of
`log_partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound_exp`. -/
theorem log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_upper_bound_exp
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ))
      ≤ (Λ.card : ℝ) * Real.log 2
        + β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound_exp
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ sharper log Z sandwich**: under `0 ≤ β·J`,
`|Λ|·log 2 + |E_Λ|·log cosh(β·J) ≤ log Z_Λ ≤ |Λ|·log 2 + β·J·|E_Λ|`. -/
theorem log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_sandwich_exp
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (Λ.card : ℝ) * Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ))
      ≤ (Λ.card : ℝ) * Real.log 2
        + β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_sandwich_exp
    (IsingModel.latticeGraph d) Λ J β hβJ

/-! ## Moved: ℤ^d HT Λ-layer ferromagnetic upper_bound_exp wrappers

The three ferromagnetic Λ-layer sharper-exp HT upper-bound wrappers
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic`,
`log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic`,
`freeEnergyΛ_latticeGraph_high_temp_h_zero_upper_bound_exp_ferromagnetic`
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsExpSharperFerro`.
The earlier import path is preserved by re-importing the new child. -/


/-! ## Moved: ℤ^d HT Λ-layer sandwich_exp wrappers

The 4 ℤ^d Λ-layer sandwich_exp HT wrappers
(`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_sandwich_exp`,
`_ferromagnetic`,
`freeEnergyΛ_latticeGraph_high_temp_h_zero_sandwich_exp`,
`_ferromagnetic`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsExpSharperSandwich`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: ℤ^d HT Λ-layer complete_summary_exp wrappers

The 6 ℤ^d Λ-layer `*_complete_summary_exp` HT wrappers (3 base:
`partitionFunctionΛ_*`, `freeEnergyΛ_*`, `log_partitionFunctionΛ_*`;
plus 3 `_ferromagnetic` variants) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsExpSharperCompleteSummary`.
The earlier import path is preserved by re-importing the new child.
-/

end Ambient

end IsingModel
