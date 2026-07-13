import IsingModel.Lattice
import IsingModel.AmbientLattice.BetaDerivative
import IsingModel.AmbientLattice.BetaDerivativePartitionSusc
import IsingModel.AmbientLattice.JDerivative
import IsingModel.AmbientLattice.FieldDerivative

/-!
# Concrete susceptibility along-ex hasDerivAt wrappers (GJ §17.5–§17.6)

Narrow child module for four ℤ^d
`susceptibilityAlongExhaustion_latticeGraph_hasDerivAt_*` wrappers
(at h = 0 in β, general-h β, J, field). Each wrapper is a thin
pass-through to the corresponding ambient `susceptibility*_hasDerivAt_*`
lemma at `IsingModel.latticeGraph d`.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

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
