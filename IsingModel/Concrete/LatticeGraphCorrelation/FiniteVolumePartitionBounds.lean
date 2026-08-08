import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Positivity of the finite-volume partition function in ℤ^d and its dependence on `|h|`

Records that the partition function of the subgraph induced by the nearest-neighbor lattice
graph on a finite `Λ ⊆ ℤ^d` depends on the external field only through its absolute value,
and that it is positive, hence nonzero, being a sum of exponentials over a nonempty
configuration space. No hypothesis is imposed in any of these statements; in particular
positivity needs no sign condition on the coupling, the field or the inverse temperature.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d partitionFunction_eq_abs_h direct** at Λ-induced. -/
theorem partitionFunction_eq_abs_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, β⟩ : IsingParams ℝ)
      = IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_eq_abs_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β

/-- **ℤ^d partitionFunction_pos direct** at Λ-induced: `0 < Z_Λ`. -/
theorem partitionFunction_pos_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    0 < IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.partitionFunction_pos
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d partitionFunction_ne_zero direct** at Λ-induced. -/
theorem partitionFunction_ne_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p ≠ 0 :=
  IsingModel.partitionFunction_ne_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

end Ambient
end IsingModel
