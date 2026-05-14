import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerEpsilonPositivity

/-!
# Concrete along-ex polymerFreeEnergyAlongExhaustion tanh _iff wrappers

Narrow child module for 2 ℤ^d along-exhaustion
`polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_*_iff`
positivity / equality wrappers extracted from
`MayerEpsilonPositivityAlongEx.lean`:

* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_pos_iff`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_eq_zero_iff`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.polymerFreeEnergyAlongExhaustion_tanh_{pos,eq_zero}_iff` lemma
at `G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `MayerEpsilonPositivityAlongEx` declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d along-ex: 0 < polymerFreeEnergy(tanh) ↔ 0 < tanh ∧
allPolymers ≠ ∅**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_pos_iff
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    0 < IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n))).Nonempty :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_pos_iff
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: polymerFreeEnergy(tanh) = 0 ↔ tanh = 0 ∨
allPolymers = ∅**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_eq_zero_iff
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)) = ∅ :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_eq_zero_iff
    (IsingModel.latticeGraph d) Λ hβJ n


end Ambient
end IsingModel
