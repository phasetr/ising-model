import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d along-exhaustion correlations converging to their supremum

Concrete `latticeGraph d` statements that, for a parameter record satisfying `Ferromagnetic`
and a fixed finite subset `A` of `Fin d → ℤ`, the along-exhaustion correlation sequence of
`A` converges to its own supremum over the stages, and equally to the infinite-volume
correlation of `A`. The supremum form and the infinite-volume form are each stated along an
arbitrary `Ambient.Exhaustion` of `Fin d → ℤ` and at `Ambient.cubicExhaustion d`. No
statement here carries any hypothesis beyond `Ferromagnetic`, and none takes an instance
argument.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d correlationAlongExhaustion → ciSup** (any Exhaustion). -/
theorem correlationAlongExhaustion_latticeGraph_tendsto_ciSup_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    Filter.Tendsto
      (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A)
      Filter.atTop
      (nhds (⨆ n, correlationAlongExhaustion (IsingModel.latticeGraph d)
        Λ p A n)) :=
  correlationAlongExhaustion_tendsto_ciSup (IsingModel.latticeGraph d) Λ p hf A

/-- **ℤ^d correlationAlongExhaustion → ciSup**. -/
theorem correlationAlongExhaustion_latticeGraph_tendsto_ciSup
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    Filter.Tendsto
      (correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A)
      Filter.atTop
      (nhds (⨆ n, correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n)) :=
  correlationAlongExhaustion_tendsto_ciSup (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A

/-- **ℤ^d correlationAlongExhaustion → correlationInfinite**. -/
theorem tendsto_correlationAlongExhaustion_correlationInfinite_latticeGraph
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    Filter.Tendsto
      (correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A)
      Filter.atTop
      (nhds (correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A)) :=
  tendsto_correlationAlongExhaustion_correlationInfinite
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf A

/-- **ℤ^d correlationAlongExhaustion → correlationInfinite** (any Exhaustion). -/
theorem tendsto_correlationAlongExhaustion_correlationInfinite_latticeGraph_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    Filter.Tendsto
      (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A)
      Filter.atTop
      (nhds (correlationInfinite (IsingModel.latticeGraph d) Λ p A)) :=
  tendsto_correlationAlongExhaustion_correlationInfinite
    (IsingModel.latticeGraph d) Λ p hf A

end Ambient
end IsingModel
