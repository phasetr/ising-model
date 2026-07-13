import IsingModel.Lattice
import IsingModel.AmbientLattice.BetaDerivative
import IsingModel.AmbientLattice.BetaDerivativeMagnetization
import IsingModel.AmbientLattice.JDerivative
import IsingModel.AmbientLattice.FieldDerivative

/-!
# ℤ^d magnetizationAlongExhaustion hasDerivAt wrappers

Narrow child module for four ℤ^d
`magnetizationAlongExhaustion_latticeGraph_hasDerivAt_*` wrappers
extracted from `RegularityAlongEx.lean`:

* `magnetizationAlongExhaustion_latticeGraph_hasDerivAt_beta`,
* `magnetizationAlongExhaustion_latticeGraph_hasDerivAt_beta_general_h`,
* `magnetizationAlongExhaustion_latticeGraph_hasDerivAt_J`,
* `magnetizationAlongExhaustion_latticeGraph_hasDerivAt_field`.
-/

namespace IsingModel
namespace Ambient

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

end Ambient
end IsingModel
