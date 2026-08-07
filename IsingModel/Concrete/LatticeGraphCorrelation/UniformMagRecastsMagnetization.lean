import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d magnetization and free-energy `apply` wrappers

Unfolds the along-exhaustion and infinite-volume magnetization, and the infinite-volume free
energy, at `IsingModel.latticeGraph d` into the expressions they are defined by, including
the stagewise case split on membership in the exhaustion volume.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d magnetizationAlongExhaustion unfolding**:
`magnetizationAlongExhaustion G Λ p i n = correlationAlongExhaustion G Λ p {i} n`. -/
theorem magnetizationAlongExhaustion_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n
      = correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {i} n :=
  magnetizationAlongExhaustion_apply (IsingModel.latticeGraph d) Λ p i n

/-- **ℤ^d magnetizationAlongExhaustion `of_mem` unfolding**. -/
theorem magnetizationAlongExhaustion_latticeGraph_of_mem
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {i : Fin d → ℤ} {n : ℕ} (hi : i ∈ Λ.volume n) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n
      = correlationΛ (IsingModel.latticeGraph d) (Λ.volume n) p
          (liftFinset {i} (Finset.singleton_subset_iff.mpr hi)) :=
  magnetizationAlongExhaustion_of_mem (IsingModel.latticeGraph d) Λ p hi

/-- **ℤ^d magnetizationAlongExhaustion `of_not_mem` unfolding**. -/
theorem magnetizationAlongExhaustion_latticeGraph_of_not_mem
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {i : Fin d → ℤ} {n : ℕ} (hi : i ∉ Λ.volume n) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n = 0 :=
  magnetizationAlongExhaustion_of_not_mem (IsingModel.latticeGraph d) Λ p hi

/-- **ℤ^d `magnetizationInfinite_apply`** unfolding. -/
theorem magnetizationInfinite_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ p i
      = correlationInfinite (IsingModel.latticeGraph d) Λ p {i} :=
  magnetizationInfinite_apply (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `freeEnergyInfinite_apply`** unfolding (limsup form). -/
theorem freeEnergyInfinite_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (p : IsingParams ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ p
      = Filter.limsup
          (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p)
          Filter.atTop :=
  freeEnergyInfinite_apply (IsingModel.latticeGraph d) Λ p


end Ambient
end IsingModel
