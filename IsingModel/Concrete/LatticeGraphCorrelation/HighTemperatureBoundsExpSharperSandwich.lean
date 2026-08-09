import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d fixed-volume sharper sandwiches for `Z_Λ` and `f_Λ` at zero field

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ` and at the parameter
record `⟨J, 0, β⟩`, sandwiches in which the lower bound gives every edge a factor
`cosh (β * J)` and the sharper upper bound gives it `exp (β * J)` instead: the partition
function between `2 ^ |Λ| * cosh (β * J) ^ |E_Λ|` and `2 ^ |Λ| * exp (β * J * |E_Λ|)`, and the
free-energy density between `log 2 + (|E_Λ| / |Λ|) * log (cosh (β * J))` and
`log 2 + β * J * |E_Λ| / |Λ|`. Each appears under `0 ≤ β * J` and in a ferromagnetic form
under `0 ≤ J` together with `0 < β`; the free-energy statements, and they alone, also need `Λ`
nonempty.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ sharper Z high-temp sandwich**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_sandwich_exp
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ Λ.card *
          Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_sandwich_exp
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ sharper f high-temp sandwich**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_sandwich_exp
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
          Λ.card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 +
          β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
              Λ.card :=
  freeEnergyΛ_high_temp_h_zero_sandwich_exp
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d Λ ferromagnetic Z sharper sandwich**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_sandwich_exp_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ Λ.card *
          Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_sandwich_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ

/-- **ℤ^d Λ ferromagnetic f sharper sandwich**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_sandwich_exp_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
          Λ.card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 +
          β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
              Λ.card :=
  freeEnergyΛ_high_temp_h_zero_sandwich_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ hne

end Ambient

end IsingModel
