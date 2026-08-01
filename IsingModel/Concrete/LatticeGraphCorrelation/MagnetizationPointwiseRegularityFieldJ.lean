import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.Magnetization

/-!
# ℤ^d `magnetizationAlongExhaustion_latticeGraph_*At_{field,J}` wrappers

Narrow child module for four ℤ^d
`magnetizationAlongExhaustion_latticeGraph_*At_{field,J}` pointwise
wrappers extracted from `MagnetizationPointwiseRegularity.lean`:

* `magnetizationAlongExhaustion_latticeGraph_continuousAt_field`,
* `magnetizationAlongExhaustion_latticeGraph_differentiableAt_field`,
* `magnetizationAlongExhaustion_latticeGraph_continuousAt_J`,
* `magnetizationAlongExhaustion_latticeGraph_differentiableAt_J`.

Each result is a direct instantiation of the corresponding ambient pointwise
wrapper
`Ambient.magnetizationAlongExhaustion_{continuousAt,differentiableAt}_{field,J}`
(`AmbientLattice/SpecialCases/Magnetization.lean`) at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged from the
former `MagnetizationPointwiseRegularity` declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` ContinuousAt h**. -/
theorem magnetizationAlongExhaustion_latticeGraph_continuousAt_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ContinuousAt (fun h' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  Ambient.magnetizationAlongExhaustion_continuousAt_field
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` DifferentiableAt h**. -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiableAt_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    DifferentiableAt ℝ (fun h' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  Ambient.magnetizationAlongExhaustion_differentiableAt_field
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` ContinuousAt J**. -/
theorem magnetizationAlongExhaustion_latticeGraph_continuousAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ContinuousAt (fun J' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  Ambient.magnetizationAlongExhaustion_continuousAt_J
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` DifferentiableAt J**. -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiableAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    DifferentiableAt ℝ (fun J' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  Ambient.magnetizationAlongExhaustion_differentiableAt_J
    (IsingModel.latticeGraph d) Λ J h β i n

end Ambient
end IsingModel
