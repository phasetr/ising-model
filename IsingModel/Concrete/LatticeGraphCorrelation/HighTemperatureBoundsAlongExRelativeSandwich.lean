import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrictFerro

/-!
# Concrete alongExhaustion Z relative_sandwich wrappers at h = 0

Narrow child module for two ℤ^d alongExhaustion
`partitionFunctionAlongExhaustion_latticeGraph_*_relative_sandwich`
wrappers (general and ferromagnetic) at `h = 0`. Each wrapper is a thin
pass-through to the corresponding ambient
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_relative_sandwich*`
lemma at `IsingModel.latticeGraph d`.
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
