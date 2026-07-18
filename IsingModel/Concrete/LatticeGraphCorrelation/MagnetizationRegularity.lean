import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.Magnetization

/-!
# Concrete magnetization regularity wrappers

Narrow child module for concrete finite-stage magnetization `Continuous` and
`Differentiable` wrappers on the lattice graph. The theorem names are the same
as the former declarations, but callers can now avoid importing the
monolithic concrete module.
-/

namespace IsingModel
namespace Ambient

/-! ### magnetization regularity ℤ^d wraps -/

/-! ## Moved: magnetizationΛ Λ-direct regularity wrappers

The four wrappers
`magnetizationΛ_latticeGraph_continuous_field`,
`magnetizationΛ_latticeGraph_differentiable_field`,
`magnetizationΛ_latticeGraph_continuous_J`,
`magnetizationΛ_latticeGraph_differentiable_J` now live in
`MagnetizationRegularityLambda.lean`. -/


/-- **ℤ^d along-ex: magnetization Continuous in `h`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_continuous_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    Continuous (fun h' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J, h', β⟩ : IsingParams ℝ) i n) :=
  Ambient.magnetizationAlongExhaustion_continuous_field
    (IsingModel.latticeGraph d) Λ J β i n

/-- **ℤ^d along-ex: magnetization Differentiable in `h`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiable_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    Differentiable ℝ (fun h' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J, h', β⟩ : IsingParams ℝ) i n) :=
  Ambient.magnetizationAlongExhaustion_differentiable_field
    (IsingModel.latticeGraph d) Λ J β i n

/-- **ℤ^d along-ex: magnetization Continuous in `J`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_continuous_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    Continuous (fun J' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J', h, β⟩ : IsingParams ℝ) i n) :=
  Ambient.magnetizationAlongExhaustion_continuous_J
    (IsingModel.latticeGraph d) Λ h β i n

/-- **ℤ^d along-ex: magnetization Differentiable in `J`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiable_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    Differentiable ℝ (fun J' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J', h, β⟩ : IsingParams ℝ) i n) :=
  Ambient.magnetizationAlongExhaustion_differentiable_J
    (IsingModel.latticeGraph d) Λ h β i n

/-! ## Moved: magnetizationAlongExhaustion β-direction wrappers

The two `magnetizationAlongExhaustion_latticeGraph_{continuous,differentiable}_beta`
wrappers (general `h`) now live in `MagnetizationRegularityBeta.lean`. -/



end Ambient
end IsingModel
