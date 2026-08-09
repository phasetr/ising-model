import IsingModel.PhaseTransition.MagnetizationSusceptibility
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d magnetization as the correlation of a singleton

Concrete statement, on the subgraph induced by a fixed finite volume of `Fin d → ℤ` and for
an arbitrary parameter record, that the magnetization at a vertex is the correlation of the
singleton set containing that vertex. It carries no hypothesis and takes no instance
argument.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d magnetization_apply direct** (Λ-induced):
`magnetization = correlation … {i}`. -/
theorem magnetization_apply_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (i : (↑Λ : Type _)) :
    IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i
      = IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p {i} :=
  IsingModel.magnetization_apply
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i

end Ambient

end IsingModel
