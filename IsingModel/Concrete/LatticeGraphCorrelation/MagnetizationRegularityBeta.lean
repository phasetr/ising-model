import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.Magnetization

/-!
# ℤ^d along-ex magnetizationAlongExhaustion β-direction regularity wrappers

Narrow child module for two ℤ^d
`magnetizationAlongExhaustion_latticeGraph_{continuous,differentiable}_beta`
wrappers (general `h`) extracted from `MagnetizationRegularity.lean`. Each
wrapper is a thin pass-through to the corresponding ambient lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` Continuous in β** (general h). -/
theorem magnetizationAlongExhaustion_latticeGraph_continuous_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    Continuous (fun β' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J, h, β'⟩ : IsingParams ℝ) i n) :=
  Ambient.magnetizationAlongExhaustion_continuous_beta
    (IsingModel.latticeGraph d) Λ J h i n

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` Differentiable in β** (general h). -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiable_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    Differentiable ℝ (fun β' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J, h, β'⟩ : IsingParams ℝ) i n) :=
  Ambient.magnetizationAlongExhaustion_differentiable_beta
    (IsingModel.latticeGraph d) Λ J h i n

end Ambient
end IsingModel
