import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d Λ-layer HT sharper-exp ferromagnetic upper-bound wrappers

Narrow child module for three ℤ^d Λ-layer sharper-exp HT upper-bound
ferromagnetic wrappers extracted from
`HighTemperatureBoundsExpSharper.lean`:

* `partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic`,
* `log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic`,
* `freeEnergyΛ_latticeGraph_high_temp_h_zero_upper_bound_exp_ferromagnetic`.

Each result is a thin pass-through of the corresponding ambient
`*_ferromagnetic` HT bound at `G := IsingModel.latticeGraph d`. The
theorem names are unchanged from the former
`HighTemperatureBoundsExpSharper` declarations.
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
