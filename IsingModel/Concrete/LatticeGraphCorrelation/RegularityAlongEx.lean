import IsingModel.Lattice
import IsingModel.AmbientLattice.BetaDerivative
import IsingModel.AmbientLattice.JDerivative
import IsingModel.AmbientLattice.FieldDerivative

/-!
# Concrete ℤ^d along-exhaustion `hasDerivAt` wrappers (GJ §17.5–§17.6)

Narrow child module for the 18 ℤ^d along-exhaustion `hasDerivAt`
wrappers (`correlationAlongExhaustion`, `magnetizationAlongExhaustion`,
`partitionFunctionAlongExhaustion`, `freeEnergyAlongExhaustion`,
`susceptibilityAlongExhaustion` — in β/β_general_h/J/field directions)
extracted from `Regularity.lean` in PR #2042. Each is a thin
pass-through to the corresponding ambient along-exhaustion
`hasDerivAt` lemma at `IsingModel.latticeGraph d`. All wrappers are
stated in existence form `∃ d : ℝ, HasDerivAt _ d _`. The theorem
names are unchanged from the former `Regularity` declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

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

/-! ## Moved: magnetizationAlongEx hasDerivAt wrappers

The four wrappers
`magnetizationAlongExhaustion_latticeGraph_hasDerivAt_beta`,
`magnetizationAlongExhaustion_latticeGraph_hasDerivAt_beta_general_h`,
`magnetizationAlongExhaustion_latticeGraph_hasDerivAt_J`,
`magnetizationAlongExhaustion_latticeGraph_hasDerivAt_field` now live
in `RegularityAlongExMag.lean`. -/


/-! ## Moved: freeEnergy along-ex hasDerivAt wrappers

The three wrappers
`freeEnergyAlongExhaustion_latticeGraph_hasDerivAt_{beta_general_h,J,field}`
now live in `RegularityAlongExPartitionFreeEnergyFE.lean`. The three
`partitionFunctionAlongExhaustion_latticeGraph_hasDerivAt_{beta,J,field}`
wrappers were deleted; no consumer of them was found in this
repository. -/



/-! ## Moved: susceptibility along-ex hasDerivAt wrappers

The four `susceptibilityAlongExhaustion_latticeGraph_hasDerivAt_*`
wrappers now live in `RegularityAlongExSusceptibility.lean`. -/


end Ambient

end IsingModel
