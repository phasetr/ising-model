import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsBoundOnly

/-!
# Concrete alongExhaustion Z ratio_bound J = 0 / β = 0 slice wrappers at h = 0

Narrow child module for four ℤ^d alongExhaustion
`partitionFunctionAlongExhaustion_latticeGraph_*_ratio_bound` slice
wrappers (J = 0 and β = 0 trivial slices, with ferromagnetic variants)
at `h = 0`. Each wrapper is a thin pass-through to the corresponding
ambient `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound*`
lemma at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d along-ex Z ratio upper bound at J=0, stage `n`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_ratio_bound
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-ex Z ratio upper bound at β=0, stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ) n
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-ex ferromagnetic Z ratio upper bound at J=0, stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_ratio_bound_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n

/-- **ℤ^d along-ex ferromagnetic Z ratio upper bound at β=0, stage `n`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_h_zero_ratio_bound_beta_zero_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ) n
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n

end Ambient
end IsingModel
