import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d fixed-volume partition function relative to the free-spin count

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ` and at the parameter
record `⟨J, 0, β⟩`, the sandwich of the partition function divided by `2 ^ |Λ|` between
`cosh (β * J) ^ |E_Λ|` and `exp (β * J * |E_Λ|)`. The sandwich is stated under `0 ≤ β * J` and
again in a ferromagnetic form under `0 ≤ J` together with `0 < β`; no nonemptiness or
edge-count condition enters.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d Λ Z relative-deviation sandwich**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_relative_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) / (2 : ℝ) ^ Λ.card ∧
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) / (2 : ℝ) ^ Λ.card
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_relative_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ ferromagnetic Z relative-deviation sandwich**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_relative_sandwich_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) / (2 : ℝ) ^ Λ.card ∧
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) / (2 : ℝ) ^ Λ.card
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_relative_sandwich_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ

end Ambient

end IsingModel
