import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Regularity.HasDerivCorr

/-!
# ℤ^d Λ-layer magnetizationΛ hasDerivAt wrappers

Narrow child module for four ℤ^d Λ-layer
`magnetizationΛ_latticeGraph_hasDerivAt_*` wrappers extracted from
`RegularityMagSusc.lean`:

* `magnetizationΛ_latticeGraph_hasDerivAt_field`,
* `magnetizationΛ_latticeGraph_hasDerivAt_beta`,
* `magnetizationΛ_latticeGraph_hasDerivAt_beta_general_h`,
* `magnetizationΛ_latticeGraph_hasDerivAt_J`.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: `magnetizationΛ` HasDerivAt in h**. -/
theorem magnetizationΛ_latticeGraph_hasDerivAt_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i) c h :=
  ⟨_, Ambient.magnetizationΛ_hasDerivAt_field
    (IsingModel.latticeGraph d) Λ J h β i⟩

/-- **ℤ^d Λ: `magnetizationΛ` HasDerivAt in β at h = 0**. -/
theorem magnetizationΛ_latticeGraph_hasDerivAt_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) i) c β :=
  ⟨_, Ambient.magnetizationΛ_hasDerivAt_beta
    (IsingModel.latticeGraph d) Λ J β i⟩

/-- **ℤ^d Λ: `magnetizationΛ` HasDerivAt in β at general h**. -/
theorem magnetizationΛ_latticeGraph_hasDerivAt_beta_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i) c β :=
  ⟨_, Ambient.magnetizationΛ_hasDerivAt_beta_general_h
    (IsingModel.latticeGraph d) Λ J h β i⟩

/-- **ℤ^d Λ: `magnetizationΛ` HasDerivAt in J**. -/
theorem magnetizationΛ_latticeGraph_hasDerivAt_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i) c J :=
  ⟨_, Ambient.magnetizationΛ_hasDerivAt_J
    (IsingModel.latticeGraph d) Λ J h β i⟩

end Ambient
end IsingModel
