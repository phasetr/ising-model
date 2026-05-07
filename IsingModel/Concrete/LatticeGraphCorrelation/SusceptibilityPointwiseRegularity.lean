import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularity

/-!
# Concrete pointwise regularity wrappers for lattice susceptibility

This module contains concrete `latticeGraph` specializations of ambient
`ContinuousAt` and `DifferentiableAt` APIs for per-parameter
`susceptibilityAlongExhaustion` regularity. It is split out of the legacy
concrete correlation module so future susceptibility pointwise work can build a
narrower child path.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ### ℤ^d along-ex pointwise susceptibility wrappers -/

/-- **ℤ^d along-ex: `susceptibilityAlongExhaustion` ContinuousAt β at general h**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_continuousAt_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ContinuousAt (fun β' =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  Ambient.susceptibilityAlongExhaustion_continuousAt_beta_gen
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `susceptibilityAlongExhaustion` DifferentiableAt β at general h**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_differentiableAt_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    DifferentiableAt ℝ (fun β' =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  Ambient.susceptibilityAlongExhaustion_differentiableAt_beta_gen
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `susceptibilityAlongExhaustion` ContinuousAt h**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_continuousAt_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ContinuousAt (fun h' =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  Ambient.susceptibilityAlongExhaustion_continuousAt_field_gen
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `susceptibilityAlongExhaustion` DifferentiableAt h**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_differentiableAt_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    DifferentiableAt ℝ (fun h' =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  Ambient.susceptibilityAlongExhaustion_differentiableAt_field_gen
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `susceptibilityAlongExhaustion` ContinuousAt J**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_continuousAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ContinuousAt (fun J' =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  Ambient.susceptibilityAlongExhaustion_continuousAt_J_gen
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `susceptibilityAlongExhaustion` DifferentiableAt J**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_differentiableAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    DifferentiableAt ℝ (fun J' =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  Ambient.susceptibilityAlongExhaustion_differentiableAt_J_gen
    (IsingModel.latticeGraph d) Λ J h β i n

end Ambient
end IsingModel
