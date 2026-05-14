import IsingModel.Lattice
import IsingModel.AmbientLattice.BetaDerivative
import IsingModel.AmbientLattice.BetaDerivativeMagnetization

/-!
# ℤ^d `magnetizationAlongExhaustion_latticeGraph_*At_{field,J}` wrappers

Narrow child module for four ℤ^d
`magnetizationAlongExhaustion_latticeGraph_*At_{field,J}` pointwise
wrappers extracted from `MagnetizationPointwiseRegularity.lean`:

* `magnetizationAlongExhaustion_latticeGraph_continuousAt_field`,
* `magnetizationAlongExhaustion_latticeGraph_differentiableAt_field`,
* `magnetizationAlongExhaustion_latticeGraph_continuousAt_J`,
* `magnetizationAlongExhaustion_latticeGraph_differentiableAt_J`.

Each result is derived from the corresponding ambient
`Ambient.magnetizationAlongExhaustion_{continuous,differentiable}_{field,J}_gen`
lemma at `G := IsingModel.latticeGraph d` via `.continuousAt` /
`.differentiableAt`. The theorem names are unchanged from the former
`MagnetizationPointwiseRegularity` declarations.
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
  (Ambient.magnetizationAlongExhaustion_continuous_field_gen
    (IsingModel.latticeGraph d) Λ J β i n).continuousAt

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` DifferentiableAt h**. -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiableAt_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    DifferentiableAt ℝ (fun h' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  (Ambient.magnetizationAlongExhaustion_differentiable_field_gen
    (IsingModel.latticeGraph d) Λ J β i n).differentiableAt

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` ContinuousAt J**. -/
theorem magnetizationAlongExhaustion_latticeGraph_continuousAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ContinuousAt (fun J' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  (Ambient.magnetizationAlongExhaustion_continuous_J_gen
    (IsingModel.latticeGraph d) Λ h β i n).continuousAt

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` DifferentiableAt J**. -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiableAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    DifferentiableAt ℝ (fun J' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  (Ambient.magnetizationAlongExhaustion_differentiable_J_gen
    (IsingModel.latticeGraph d) Λ h β i n).differentiableAt

end Ambient
end IsingModel
