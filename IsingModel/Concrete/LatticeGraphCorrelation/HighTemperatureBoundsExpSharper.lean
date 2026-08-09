import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d fixed-volume sharper upper bounds and the `log Z_Λ` sandwich at zero field

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ` and at the parameter
record `⟨J, 0, β⟩`, the upper bounds in which each edge contributes `exp (β * J)`: the
partition function below `2 ^ |Λ| * exp (β * J * |E_Λ|)`, its logarithm below
`|Λ| * log 2 + β * J * |E_Λ|`, and the free-energy density below
`log 2 + β * J * |E_Λ| / |Λ|`; together with the sandwich placing `log Z_Λ` above
`|Λ| * log 2 + |E_Λ| * log (cosh (β * J))` as well. Every statement here assumes `0 ≤ β * J`,
and the free-energy bound alone also assumes `Λ` nonempty.
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

end Ambient

end IsingModel
