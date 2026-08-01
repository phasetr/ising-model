import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.Magnetization

/-!
# Concrete pointwise regularity wrappers for lattice magnetization

This module contains concrete `latticeGraph` specializations of ambient
`ContinuousAt` and `DifferentiableAt` APIs for per-parameter
`magnetizationAlongExhaustion` regularity. It is split out of the original
concrete correlation module so future magnetization pointwise work can build a
narrower child path.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ### ℤ^d along-ex pointwise magnetization wrappers -/

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` ContinuousAt β** (general h). -/
theorem magnetizationAlongExhaustion_latticeGraph_continuousAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ContinuousAt (fun β' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  Ambient.magnetizationAlongExhaustion_continuousAt_beta
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` DifferentiableAt β** (general h). -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiableAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    DifferentiableAt ℝ (fun β' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  Ambient.magnetizationAlongExhaustion_differentiableAt_beta
    (IsingModel.latticeGraph d) Λ J h β i n

/-! ## Moved: field/J pointwise wrappers

The four wrappers
`magnetizationAlongExhaustion_latticeGraph_continuousAt_field`,
`magnetizationAlongExhaustion_latticeGraph_differentiableAt_field`,
`magnetizationAlongExhaustion_latticeGraph_continuousAt_J`,
`magnetizationAlongExhaustion_latticeGraph_differentiableAt_J` now
live in `MagnetizationPointwiseRegularityFieldJ.lean`. -/


end Ambient
end IsingModel
