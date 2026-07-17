import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Regularity.HasDerivCorr

/-!
# Concrete ℤ^d Λ-layer `magnetizationΛ`/`susceptibilityΛ` `hasDerivAt` wrappers

Narrow child module for the 8 ℤ^d Λ-layer
`magnetizationΛ_latticeGraph_hasDerivAt_*` and
`susceptibilityΛ_latticeGraph_hasDerivAt_*` wrappers (in field/β/
β_general_h/J directions) extracted from `Regularity.lean` in
PR #2043. Each is a thin pass-through to the corresponding ambient
`magnetizationΛ_hasDerivAt_*` / `susceptibilityΛ_hasDerivAt_*` lemma
at `IsingModel.latticeGraph d`. All wrappers are stated in existence
form `∃ c : ℝ, HasDerivAt _ c _`. The theorem names are unchanged
from the former `Regularity` declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## Moved: Λ-layer magnetizationΛ hasDerivAt wrappers

The four wrappers
`magnetizationΛ_latticeGraph_hasDerivAt_field`,
`magnetizationΛ_latticeGraph_hasDerivAt_beta`,
`magnetizationΛ_latticeGraph_hasDerivAt_beta_general_h`,
`magnetizationΛ_latticeGraph_hasDerivAt_J` now live in
`RegularityMagSuscMagnetization.lean`. -/


/-- **ℤ^d Λ: `susceptibilityΛ` HasDerivAt in β at h = 0**. -/
theorem susceptibilityΛ_latticeGraph_hasDerivAt_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) i) c β :=
  ⟨_, Ambient.susceptibilityΛ_hasDerivAt_beta
    (IsingModel.latticeGraph d) Λ J β i⟩

/-- **ℤ^d Λ: `susceptibilityΛ` HasDerivAt in β at general h**. -/
theorem susceptibilityΛ_latticeGraph_hasDerivAt_beta_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i) c β :=
  ⟨_, Ambient.susceptibilityΛ_hasDerivAt_beta_general_h
    (IsingModel.latticeGraph d) Λ J h β i⟩

/-- **ℤ^d Λ: `susceptibilityΛ` HasDerivAt in J**. -/
theorem susceptibilityΛ_latticeGraph_hasDerivAt_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i) c J :=
  ⟨_, Ambient.susceptibilityΛ_hasDerivAt_J
    (IsingModel.latticeGraph d) Λ J h β i⟩

/-- **ℤ^d Λ: `susceptibilityΛ` HasDerivAt in h**. -/
theorem susceptibilityΛ_latticeGraph_hasDerivAt_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i) c h :=
  ⟨_, Ambient.susceptibilityΛ_hasDerivAt_field
    (IsingModel.latticeGraph d) Λ J h β i⟩

end Ambient

end IsingModel
