import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaEpsilonIff

/-!
# Concrete Λ-direct polymerFreeEnergy_Λ tanh positivity / equality wrappers

Narrow child module for 2 ℤ^d Λ-direct
`polymerFreeEnergy_Λ_latticeGraph_tanh_*_iff` wrappers extracted
from `MayerEpsilonPositivity.lean`:

* `polymerFreeEnergy_Λ_latticeGraph_tanh_pos_iff`,
* `polymerFreeEnergy_Λ_latticeGraph_tanh_eq_zero_iff`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.polymerFreeEnergy_Λ_tanh_{pos,eq_zero}_iff` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `MayerEpsilonPositivity` declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d Λ: 0 < polymerFreeEnergy(tanh) ↔ 0 < tanh ∧
allPolymers ≠ ∅**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_pos_iff
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty :=
  Ambient.polymerFreeEnergy_Λ_tanh_pos_iff
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: polymerFreeEnergy(tanh) = 0 ↔ tanh = 0 ∨
allPolymers = ∅**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_eq_zero_iff
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅ :=
  Ambient.polymerFreeEnergy_Λ_tanh_eq_zero_iff
    (IsingModel.latticeGraph d) Λ hβJ

end Ambient
end IsingModel
