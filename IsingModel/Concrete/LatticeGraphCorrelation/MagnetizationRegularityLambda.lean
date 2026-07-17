import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Regularity.Defs

/-!
# ℤ^d magnetizationΛ Λ-direct regularity wrappers

Narrow child module for four ℤ^d Λ-direct
`magnetizationΛ_latticeGraph_*` continuous/differentiable wrappers
extracted from `MagnetizationRegularity.lean`:

* `magnetizationΛ_latticeGraph_continuous_field`,
* `magnetizationΛ_latticeGraph_differentiable_field`,
* `magnetizationΛ_latticeGraph_continuous_J`,
* `magnetizationΛ_latticeGraph_differentiable_J`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: magnetization Continuous in `h`**. -/
theorem magnetizationΛ_latticeGraph_continuous_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    Continuous (fun h' =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i) :=
  Ambient.magnetizationΛ_continuous_field
    (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d Λ: magnetization Differentiable in `h`**. -/
theorem magnetizationΛ_latticeGraph_differentiable_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    Differentiable ℝ (fun h' =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i) :=
  Ambient.magnetizationΛ_differentiable_field
    (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d Λ: magnetization Continuous in `J`**. -/
theorem magnetizationΛ_latticeGraph_continuous_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h β : ℝ) (i : ↑Λ) :
    Continuous (fun J' =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i) :=
  Ambient.magnetizationΛ_continuous_J
    (IsingModel.latticeGraph d) Λ h β i

/-- **ℤ^d Λ: magnetization Differentiable in `J`**. -/
theorem magnetizationΛ_latticeGraph_differentiable_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h β : ℝ) (i : ↑Λ) :
    Differentiable ℝ (fun J' =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i) :=
  Ambient.magnetizationΛ_differentiable_J
    (IsingModel.latticeGraph d) Λ h β i

end Ambient
end IsingModel
