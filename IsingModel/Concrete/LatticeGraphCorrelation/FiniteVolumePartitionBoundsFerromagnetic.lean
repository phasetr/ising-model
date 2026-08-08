import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Ferromagnetic bounds on the finite-volume partition function in ℤ^d

Records, for the subgraph induced by the nearest-neighbor lattice graph on a finite
`Λ ⊆ ℤ^d`, that the partition function increases with the absolute value of the external
field, and that under the ferromagnetic condition it is at least `1`, so that its logarithm
is nonnegative. The monotonicity statement sits in the ferromagnetic regime without taking
the ferromagnetic condition as a hypothesis: it assumes nonnegative coupling and positive
inverse temperature, and compares the two fields through `|h₁| ≤ |h₂|` rather than through
a sign condition on either.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d partitionFunction_monotone_abs_h direct** at Λ-induced
(ferromagnetic). -/
theorem partitionFunction_monotone_abs_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_monotone_abs_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hJ hβ hh

/-- **ℤ^d partitionFunction_ge_one_of_ferromagnetic direct** (Λ-induced). -/
theorem partitionFunction_ge_one_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (1 : ℝ) ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.partitionFunction_ge_one_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf

/-- **ℤ^d log_partitionFunction_nonneg_of_ferromagnetic direct** (Λ-induced). -/
theorem log_partitionFunction_nonneg_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ Real.log (IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p) :=
  IsingModel.log_partitionFunction_nonneg_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf

end Ambient
end IsingModel
