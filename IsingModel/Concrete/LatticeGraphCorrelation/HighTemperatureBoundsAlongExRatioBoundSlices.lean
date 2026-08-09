import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsBoundOnly

/-!
# ℤ^d along-exhaustion partition-function ratio bounds, one slice at a time

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ`, the separate bounds `exp (β * J * |E_n|)` on the ratio of the partition function
at `⟨J, 0, β⟩` to its value at `⟨0, 0, β⟩` and on the ratio to its value at `⟨J, 0, 0⟩`. Each
ratio is bounded under `0 ≤ β * J` and again under the ferromagnetic pair `0 ≤ J` and
`0 < β`; no nonemptiness or edge-count condition enters any statement here.
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
