import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrictFerro

/-!
# ℤ^d along-exhaustion partition function relative to the free-spin count

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ` and at the parameter record `⟨J, 0, β⟩`, the sandwich of the partition function
divided by `2 ^ |Λ_n|` between `cosh (β * J) ^ |E_n|` and `exp (β * J * |E_n|)`. The sandwich
is stated under `0 ≤ β * J` and again in a ferromagnetic form under `0 ≤ J` together with
`0 < β`; no condition on `Λ.volume n` or on the stage-`n` edge count enters.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d along-ex Z relative-deviation sandwich at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_relative_sandwich
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n / (2 : ℝ) ^ (Λ.volume n).card ∧
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n / (2 : ℝ) ^ (Λ.volume n).card
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_relative_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-ex ferromagnetic Z relative-deviation sandwich at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_h_zero_relative_sandwich_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n / (2 : ℝ) ^ (Λ.volume n).card ∧
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n / (2 : ℝ) ^ (Λ.volume n).card
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_relative_sandwich_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n

end Ambient
end IsingModel
