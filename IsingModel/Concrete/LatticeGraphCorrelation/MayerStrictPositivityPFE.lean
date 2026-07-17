import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaEpsilonIff

/-!
# Concrete Λ-direct polymerFreeEnergy_Λ positivity wrappers

Narrow child module for 2 ℤ^d Λ-direct
`polymerFreeEnergy_Λ_*_pos_of_*_polymers_nonempty` positivity wrappers
extracted from `MayerStrictPositivity.lean`:

* `polymerFreeEnergy_Λ_latticeGraph_pos_of_t_pos_of_polymers_nonempty`,
* `polymerFreeEnergy_Λ_latticeGraph_tanh_pos_of_tanh_pos_of_polymers_nonempty`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.polymerFreeEnergy_Λ_*_pos_of_*_polymers_nonempty` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `MayerStrictPositivity` declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d Λ: 0 < pFE under `0 < t` and polymers exist**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_pos_of_t_pos_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty) :
    0 < IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t :=
  Ambient.polymerFreeEnergy_Λ_pos_of_t_pos_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_t_pos h_poly

/-- **ℤ^d Λ: 0 < pFE(tanh) under `0 < tanh` and polymers exist**. -/
theorem
polymerFreeEnergy_Λ_latticeGraph_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J))
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty) :
    0 < IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (Real.tanh (β * J)) :=
  Ambient.polymerFreeEnergy_Λ_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_tanh_pos h_poly

end Ambient
end IsingModel
