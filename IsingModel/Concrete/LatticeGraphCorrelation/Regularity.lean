import IsingModel.Concrete.IntLattice
import IsingModel.AmbientLattice.BetaDerivative
import IsingModel.AmbientLattice.JDerivative
import IsingModel.AmbientLattice.FieldDerivative

/-!
# Concrete regularity wrappers for the ℤ^d Ising correlation

This module contains concrete latticeGraph specializations of ambient derivative,
continuity, differentiability, and analyticity APIs. It is split out of the
legacy concrete correlation module so future regularity work can build a
narrower child path instead of touching the monolithic legacy file.
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

/-! ### ℤ^d along-exhaustion `hasDerivAt` wrappers (GJ §17.5–§17.6)

Direct instantiations at `G := IsingModel.latticeGraph d` of the
along-exhaustion `hasDerivAt` family
(`AmbientLattice/BetaDerivative.lean`,
`AmbientLattice/JDerivative.lean`,
`AmbientLattice/FieldDerivative.lean`; PR #1628 + earlier). -/

/-- **ℤ^d along-ex: `correlationAlongExhaustion` HasDerivAt in β at h = 0**. -/
theorem correlationAlongExhaustion_latticeGraph_hasDerivAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) A n) c β :=
  Ambient.correlationAlongExhaustion_hasDerivAt_beta
    (IsingModel.latticeGraph d) Λ J β A n

/-- **ℤ^d along-ex: `correlationAlongExhaustion` HasDerivAt in β at general h**. -/
theorem correlationAlongExhaustion_latticeGraph_hasDerivAt_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) A n) c β :=
  Ambient.correlationAlongExhaustion_hasDerivAt_beta_general_h_gen
    (IsingModel.latticeGraph d) Λ J h β A n

/-- **ℤ^d along-ex: `correlationAlongExhaustion` HasDerivAt in J**. -/
theorem correlationAlongExhaustion_latticeGraph_hasDerivAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J', h, β⟩ : IsingParams ℝ) A n) c J :=
  Ambient.correlationAlongExhaustion_hasDerivAt_J
    (IsingModel.latticeGraph d) Λ J h β A n

/-- **ℤ^d along-ex: `correlationAlongExhaustion` HasDerivAt in h**. -/
theorem correlationAlongExhaustion_latticeGraph_hasDerivAt_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h', β⟩ : IsingParams ℝ) A n) c h :=
  Ambient.correlationAlongExhaustion_hasDerivAt_field
    (IsingModel.latticeGraph d) Λ J h β A n

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` HasDerivAt in β at h = 0**. -/
theorem magnetizationAlongExhaustion_latticeGraph_hasDerivAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) i n) c β :=
  Ambient.magnetizationAlongExhaustion_hasDerivAt_beta
    (IsingModel.latticeGraph d) Λ J β i n

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` HasDerivAt in β at general h**. -/
theorem magnetizationAlongExhaustion_latticeGraph_hasDerivAt_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) c β :=
  Ambient.magnetizationAlongExhaustion_hasDerivAt_beta_general_h_gen
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` HasDerivAt in J**. -/
theorem magnetizationAlongExhaustion_latticeGraph_hasDerivAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i n) c J :=
  Ambient.magnetizationAlongExhaustion_hasDerivAt_J
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` HasDerivAt in h**. -/
theorem magnetizationAlongExhaustion_latticeGraph_hasDerivAt_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) c h :=
  Ambient.magnetizationAlongExhaustion_hasDerivAt_field
    (IsingModel.latticeGraph d) Λ J h β i n

/-! ### ℤ^d along-ex `partitionFunctionAlongExhaustion` /
`freeEnergyAlongExhaustion` `hasDerivAt` wrappers -/

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` HasDerivAt in β**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_hasDerivAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) n) c β :=
  Ambient.partitionFunctionAlongExhaustion_hasDerivAt_beta
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` HasDerivAt in J**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_hasDerivAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J', h, β⟩ : IsingParams ℝ) n) c J :=
  Ambient.partitionFunctionAlongExhaustion_hasDerivAt_J
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` HasDerivAt in h**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_hasDerivAt_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h', β⟩ : IsingParams ℝ) n) c h :=
  Ambient.partitionFunctionAlongExhaustion_hasDerivAt_field
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` HasDerivAt in β at general h**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_hasDerivAt_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) n) c β :=
  Ambient.freeEnergyAlongExhaustion_hasDerivAt_beta_general_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` HasDerivAt in J**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_hasDerivAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J', h, β⟩ : IsingParams ℝ) n) c J :=
  Ambient.freeEnergyAlongExhaustion_hasDerivAt_J
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` HasDerivAt in h**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_hasDerivAt_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h', β⟩ : IsingParams ℝ) n) c h :=
  Ambient.freeEnergyAlongExhaustion_hasDerivAt_field
    (IsingModel.latticeGraph d) Λ J h β n


/-! ### ℤ^d along-ex `susceptibilityAlongExhaustion` `hasDerivAt`
wrappers (GJ §17.5–§17.6) -/

/-- **ℤ^d along-ex: `susceptibilityAlongExhaustion` HasDerivAt in β at h = 0**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_hasDerivAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) i n) c β :=
  Ambient.susceptibilityAlongExhaustion_hasDerivAt_beta_gen
    (IsingModel.latticeGraph d) Λ J β i n


/-- **ℤ^d along-ex: `susceptibilityAlongExhaustion` HasDerivAt in β at general h**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_hasDerivAt_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) c β :=
  Ambient.susceptibilityAlongExhaustion_hasDerivAt_beta_general_h_gen
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `susceptibilityAlongExhaustion` HasDerivAt in J**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_hasDerivAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i n) c J :=
  Ambient.susceptibilityAlongExhaustion_hasDerivAt_J_gen
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `susceptibilityAlongExhaustion` HasDerivAt in h**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_hasDerivAt_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) c h :=
  Ambient.susceptibilityAlongExhaustion_hasDerivAt_field_gen
    (IsingModel.latticeGraph d) Λ J h β i n


end Ambient

end IsingModel
