import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d fixed-volume free-energy deviation bound at zero field

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ` and at the parameter
record `⟨J, 0, β⟩`, the bound `f_Λ - log 2 ≤ β * J * |E_Λ| / |Λ|` on the free-energy density.
It is stated under `0 ≤ β * J` and again in a ferromagnetic form under `0 ≤ J` together with
`0 < β`, and each form also assumes `Λ` nonempty.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Λ sharper f deviation bound**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_deviation_bound_exp
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  freeEnergyΛ_high_temp_h_zero_deviation_bound_exp
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d Λ ferromagnetic f deviation bound**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_deviation_bound_exp_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  freeEnergyΛ_high_temp_h_zero_deviation_bound_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ hne

end Ambient

end IsingModel
