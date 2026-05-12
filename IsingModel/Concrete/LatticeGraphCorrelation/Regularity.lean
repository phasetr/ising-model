import IsingModel.Lattice
import IsingModel.AmbientLattice.BetaDerivative
import IsingModel.AmbientLattice.JDerivative
import IsingModel.AmbientLattice.FieldDerivative

/-!
# Concrete regularity wrappers for the ℤ^d Ising correlation

This module contains concrete `latticeGraph` specializations of ambient
`HasDerivAt` APIs. It is split out of the legacy concrete correlation module
so future derivative-wrapper work can build a narrower child path instead of
touching the monolithic legacy file.
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

/-- **ℤ^d Λ: `freeEnergyΛ` HasDerivAt in β at general h**. -/
theorem hasDerivAt_freeEnergyΛ_latticeGraph_beta_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β'⟩ : IsingParams ℝ)) c β :=
  ⟨_, Ambient.hasDerivAt_freeEnergyΛ_beta_general_h
    (IsingModel.latticeGraph d) Λ J h β⟩

/-- **ℤ^d Λ: `freeEnergyΛ` HasDerivAt in J**. -/
theorem hasDerivAt_freeEnergyΛ_latticeGraph_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J', h, β⟩ : IsingParams ℝ)) c J :=
  ⟨_, Ambient.hasDerivAt_freeEnergyΛ_J
    (IsingModel.latticeGraph d) Λ J h β⟩

/-- **ℤ^d Λ: `freeEnergyΛ` HasDerivAt in h**. -/
theorem hasDerivAt_freeEnergyΛ_latticeGraph_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h', β⟩ : IsingParams ℝ)) c h :=
  ⟨_, Ambient.hasDerivAt_freeEnergyΛ_field
    (IsingModel.latticeGraph d) Λ J h β⟩

/-- **ℤ^d Λ: `partitionFunctionΛ` HasDerivAt in β**. -/
theorem hasDerivAt_partitionFunctionΛ_latticeGraph_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β'⟩ : IsingParams ℝ)) c β :=
  ⟨_, Ambient.hasDerivAt_partitionFunctionΛ_beta
    (IsingModel.latticeGraph d) Λ J h β⟩

/-- **ℤ^d Λ: `partitionFunctionΛ` HasDerivAt in J**. -/
theorem hasDerivAt_partitionFunctionΛ_latticeGraph_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J', h, β⟩ : IsingParams ℝ)) c J :=
  ⟨_, Ambient.hasDerivAt_partitionFunctionΛ_J
    (IsingModel.latticeGraph d) Λ J h β⟩

/-- **ℤ^d Λ: `partitionFunctionΛ` HasDerivAt in h**. -/
theorem hasDerivAt_partitionFunctionΛ_latticeGraph_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h', β⟩ : IsingParams ℝ)) c h :=
  ⟨_, Ambient.hasDerivAt_partitionFunctionΛ_field
    (IsingModel.latticeGraph d) Λ J h β⟩

/-- **ℤ^d Λ: ambient-induced Boltzmann weight HasDerivAt in β**
(per-configuration, lifted from `IsingModel.boltzmannWeight`). -/
theorem hasDerivAt_boltzmannWeightΛ_latticeGraph_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (σ : Config (↑Λ : Type _)) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        IsingModel.boltzmannWeight
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β'⟩ : IsingParams ℝ) σ) c β :=
  ⟨_, Ambient.hasDerivAt_boltzmannWeightΛ_beta
    (IsingModel.latticeGraph d) Λ J h β σ⟩

/-- **ℤ^d Λ: ambient-induced Boltzmann weight HasDerivAt in J**. -/
theorem hasDerivAt_boltzmannWeightΛ_latticeGraph_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (σ : Config (↑Λ : Type _)) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        IsingModel.boltzmannWeight
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J', h, β⟩ : IsingParams ℝ) σ) c J :=
  ⟨_, Ambient.hasDerivAt_boltzmannWeightΛ_J
    (IsingModel.latticeGraph d) Λ J h β σ⟩

/-- **ℤ^d Λ: ambient-induced Boltzmann weight HasDerivAt in h**. -/
theorem hasDerivAt_boltzmannWeightΛ_latticeGraph_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (σ : Config (↑Λ : Type _)) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        IsingModel.boltzmannWeight
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h', β⟩ : IsingParams ℝ) σ) c h :=
  ⟨_, Ambient.hasDerivAt_boltzmannWeightΛ_field
    (IsingModel.latticeGraph d) Λ J h β σ⟩

/-! ## Moved: ℤ^d Λ-layer `magnetizationΛ`/`susceptibilityΛ` `hasDerivAt` wrappers

The 8 ℤ^d Λ-layer `magnetizationΛ_latticeGraph_hasDerivAt_*` and
`susceptibilityΛ_latticeGraph_hasDerivAt_*` wrappers (in field/β/
β_general_h/J directions) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.RegularityMagSusc`.
The legacy import path is preserved by re-importing the new child.
-/


/-! ## Moved: ℤ^d along-exhaustion `hasDerivAt` wrappers

The 18 ℤ^d along-exhaustion `hasDerivAt` wrappers
(`correlationAlongExhaustion`, `magnetizationAlongExhaustion`,
`partitionFunctionAlongExhaustion`, `freeEnergyAlongExhaustion`,
`susceptibilityAlongExhaustion` — in β/β_general_h/J/field
directions) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.RegularityAlongEx`.
The legacy import path is preserved by re-importing the new child.
-/

end Ambient

end IsingModel
