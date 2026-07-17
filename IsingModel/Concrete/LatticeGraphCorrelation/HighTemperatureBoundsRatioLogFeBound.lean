import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d freeEnergyΛ ratio-bound wrappers

Narrow child module for four ℤ^d
`freeEnergyΛ_latticeGraph_high_temp_h_zero_ratio_bound*` wrappers
extracted from `HighTemperatureBoundsRatioLogFe.lean`:

* `freeEnergyΛ_latticeGraph_high_temp_h_zero_ratio_bound`,
* `freeEnergyΛ_latticeGraph_high_temp_h_zero_ratio_bound_beta_zero`,
* `freeEnergyΛ_latticeGraph_high_temp_h_zero_ratio_bound_ferromagnetic`,
* `freeEnergyΛ_latticeGraph_high_temp_h_zero_ratio_bound_beta_zero_ferromagnetic`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ f ratio bound at J=0**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_ratio_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  freeEnergyΛ_high_temp_h_zero_ratio_bound
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d Λ f ratio bound at β=0**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_ratio_bound_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  freeEnergyΛ_high_temp_h_zero_ratio_bound_beta_zero
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d Λ ferromagnetic f ratio bound at J=0**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_ratio_bound_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  freeEnergyΛ_high_temp_h_zero_ratio_bound_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ hne

/-- **ℤ^d Λ ferromagnetic f ratio bound at β=0**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_ratio_bound_beta_zero_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  freeEnergyΛ_high_temp_h_zero_ratio_bound_beta_zero_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ hne

end Ambient
end IsingModel
