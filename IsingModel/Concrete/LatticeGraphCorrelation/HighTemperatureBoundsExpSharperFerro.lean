import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d fixed-volume ferromagnetic sharper upper bounds at zero field

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ` and at the parameter
record `⟨J, 0, β⟩`, the ferromagnetic form of the upper bounds in which each edge contributes
`exp (β * J)`: the partition function below `2 ^ |Λ| * exp (β * J * |E_Λ|)`, its logarithm
below `|Λ| * log 2 + β * J * |E_Λ|`, and the free-energy density below
`log 2 + β * J * |E_Λ| / |Λ|`. Every statement here assumes `0 ≤ J` together with `0 < β`, and
the free-energy bound alone also assumes `Λ` nonempty.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Λ ferromagnetic Z/logZ/f sharper upper bounds**: under
`0 ≤ J, 0 < β`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ Λ.card *
          Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ

/-- **ℤ^d Λ ferromagnetic log Z sharper upper bound**. -/
theorem log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ))
      ≤ (Λ.card : ℝ) * Real.log 2
        + β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ

/-- **ℤ^d Λ ferromagnetic f sharper upper bound**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_upper_bound_exp_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 +
          β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
              Λ.card :=
  freeEnergyΛ_high_temp_h_zero_upper_bound_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ hne

end Ambient

end IsingModel
