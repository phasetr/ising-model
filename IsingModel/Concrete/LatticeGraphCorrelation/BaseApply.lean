import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Defining equations of the ℤ^d finite-volume and per-stage functionals

Concrete `IsingModel.latticeGraph d` unfoldings. Every equation here holds by definition,
none of them carries a hypothesis, and none of them takes an instance argument.

At a fixed finite subset of `Fin d → ℤ`, the partition function, the correlation of a site
set of that subset, and the free energy are the corresponding quantities of the graph the
subset induces. Along `Ambient.cubicExhaustion d`, the free energy and the partition
function at a stage are the finite-volume free energy and partition function at that
stage's volume; those two along-exhaustion equations are `@[simp]`, the finite-volume ones
are not.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d freeEnergyAlongExhaustion_apply unfolding**. -/
@[simp]
theorem freeEnergyAlongExhaustion_latticeGraph_apply
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n
      = freeEnergyΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) p :=
  freeEnergyAlongExhaustion_apply (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n

/-- **ℤ^d partitionFunctionAlongExhaustion_apply unfolding**. -/
@[simp]
theorem partitionFunctionAlongExhaustion_latticeGraph_apply
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n
      = partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) p :=
  partitionFunctionAlongExhaustion_apply (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n

/-- **ℤ^d `partitionFunctionΛ_apply`** unfolding. -/
theorem partitionFunctionΛ_latticeGraph_apply
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ p
      = IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  partitionFunctionΛ_apply (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `correlationΛ_apply`** unfolding. -/
theorem correlationΛ_latticeGraph_apply
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ (IsingModel.latticeGraph d) Λ p A
      = IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A :=
  correlationΛ_apply (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `freeEnergyΛ_apply`** unfolding. -/
theorem freeEnergyΛ_latticeGraph_apply
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ p
      = IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  freeEnergyΛ_apply (IsingModel.latticeGraph d) Λ p
end Ambient

end IsingModel
