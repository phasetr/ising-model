import IsingModel.Lattice
import IsingModel.AmbientLattice.BetaDerivative
import IsingModel.AmbientLattice.BetaDerivativeMagnetization

/-!
# Concrete pointwise regularity wrappers for lattice magnetization

This module contains concrete `latticeGraph` specializations of ambient
`ContinuousAt` and `DifferentiableAt` APIs for per-parameter
`magnetizationAlongExhaustion` regularity. It is split out of the legacy
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
  (Ambient.magnetizationAlongExhaustion_continuous_beta_general_h_gen
    (IsingModel.latticeGraph d) Λ J h i n).continuousAt

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` DifferentiableAt β** (general h). -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiableAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    DifferentiableAt ℝ (fun β' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  (Ambient.magnetizationAlongExhaustion_differentiable_beta_general_h_gen
    (IsingModel.latticeGraph d) Λ J h i n).differentiableAt

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
