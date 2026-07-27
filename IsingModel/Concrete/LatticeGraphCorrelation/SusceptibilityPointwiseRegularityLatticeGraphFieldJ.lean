import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularity
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityAt

/-!
# ℤ^d `susceptibilityAlongExhaustion_latticeGraph_*At_{field,J}` wrappers

Narrow child module for four ℤ^d
`susceptibilityAlongExhaustion_latticeGraph_*At_{field,J}` pointwise
wrappers:

* `susceptibilityAlongExhaustion_latticeGraph_continuousAt_field`,
* `susceptibilityAlongExhaustion_latticeGraph_differentiableAt_field`,
* `susceptibilityAlongExhaustion_latticeGraph_continuousAt_J`,
* `susceptibilityAlongExhaustion_latticeGraph_differentiableAt_J`.

Each result is a thin pass-through of the ambient
`Ambient.susceptibilityAlongExhaustion_*_gen` lemma at
`G := IsingModel.latticeGraph d`.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

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
