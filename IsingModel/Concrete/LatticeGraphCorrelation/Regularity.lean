import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Regularity.HasDerivCorr

/-!
# Concrete regularity wrappers for the ℤ^d Ising correlation

This module contains concrete `latticeGraph` specializations of ambient
`HasDerivAt` APIs. It is split out of the original concrete correlation module
so future derivative-wrapper work can build a narrower child path instead of
touching the monolithic original file.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ### ℤ^d Λ-layer `hasDerivAt` wrappers (GJ §17.5–§17.6)

Direct instantiations of the `hasDerivAt_*Λ_*` family
(PRs #1619, #1623–#1628) at `G := IsingModel.latticeGraph d`.

All wrappers are stated in existence form `∃ d : ℝ, HasDerivAt _ d _`
to avoid reproducing the long explicit-derivative formulas at the
ℤ^d concrete layer; consumers needing the explicit formula can call
the underlying `Ambient.hasDerivAt_*Λ_*` directly. -/

/-- **ℤ^d Λ: `correlationΛ` HasDerivAt in β at h = 0**. -/
theorem hasDerivAt_correlationΛ_latticeGraph_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (A : Finset (↑Λ : Type _)) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) A) c β :=
  ⟨_, Ambient.hasDerivAt_correlationΛ_beta
    (IsingModel.latticeGraph d) Λ J β A⟩

/-- **ℤ^d Λ: `correlationΛ` HasDerivAt in β at general h**. -/
theorem hasDerivAt_correlationΛ_latticeGraph_beta_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) A) c β :=
  ⟨_, Ambient.hasDerivAt_correlationΛ_beta_general_h
    (IsingModel.latticeGraph d) Λ J h β A⟩

/-- **ℤ^d Λ: `correlationΛ` HasDerivAt in J**. -/
theorem hasDerivAt_correlationΛ_latticeGraph_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        Ambient.correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J', h, β⟩ : IsingParams ℝ) A) c J :=
  ⟨_, Ambient.hasDerivAt_correlationΛ_J
    (IsingModel.latticeGraph d) Λ J h β A⟩

/-- **ℤ^d Λ: `correlationΛ` HasDerivAt in h**. -/
theorem hasDerivAt_correlationΛ_latticeGraph_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        Ambient.correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h', β⟩ : IsingParams ℝ) A) c h :=
  ⟨_, Ambient.hasDerivAt_correlationΛ_field
    (IsingModel.latticeGraph d) Λ J h β A⟩

/-! ## Moved: ℤ^d Λ-layer `freeEnergyΛ` `hasDerivAt` wrappers

The three wrappers
`hasDerivAt_freeEnergyΛ_latticeGraph_beta_general_h`,
`hasDerivAt_freeEnergyΛ_latticeGraph_J`,
`hasDerivAt_freeEnergyΛ_latticeGraph_field` now live in
`IsingModel.Concrete.LatticeGraphCorrelation.RegularityFreeEnergyLambda`.
The earlier import path is preserved by re-importing the new child. -/


/-! ## Moved: ℤ^d Λ-layer `partitionFunctionΛ`/`boltzmannWeightΛ` `hasDerivAt` wrappers

The 6 ℤ^d Λ-layer
`hasDerivAt_partitionFunctionΛ_latticeGraph_{beta,J,field}` and
`hasDerivAt_boltzmannWeightΛ_latticeGraph_{beta,J,field}` wrappers
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.RegularityPartitionBoltzmann`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: ℤ^d Λ-layer `magnetizationΛ`/`susceptibilityΛ` `hasDerivAt` wrappers

The 8 ℤ^d Λ-layer `magnetizationΛ_latticeGraph_hasDerivAt_*` and
`susceptibilityΛ_latticeGraph_hasDerivAt_*` wrappers (in field/β/
β_general_h/J directions) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.RegularityMagSusc`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: ℤ^d along-exhaustion `hasDerivAt` wrappers

The 18 ℤ^d along-exhaustion `hasDerivAt` wrappers
(`correlationAlongExhaustion`, `magnetizationAlongExhaustion`,
`partitionFunctionAlongExhaustion`, `freeEnergyAlongExhaustion`,
`susceptibilityAlongExhaustion` — in β/β_general_h/J/field
directions) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.RegularityAlongEx`.
The earlier import path is preserved by re-importing the new child.
-/

end Ambient

end IsingModel
