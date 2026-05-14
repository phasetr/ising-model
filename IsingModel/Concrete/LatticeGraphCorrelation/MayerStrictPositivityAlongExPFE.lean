import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerStrictPositivity

/-!
# Concrete along-ex polymerFreeEnergyAlongExhaustion positivity wrappers

Narrow child module for 2 ℤ^d along-exhaustion
`polymerFreeEnergyAlongExhaustion_*_pos_of_*_polymers_nonempty`
positivity wrappers extracted from `MayerStrictPositivityAlongEx.lean`:

* `polymerFreeEnergyAlongExhaustion_latticeGraph_pos_of_t_pos_of_polymers_nonempty`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_pos_of_tanh_pos_of_polymers_nonempty`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.polymerFreeEnergyAlongExhaustion_*_pos_of_*_polymers_nonempty`
lemma at `G := IsingModel.latticeGraph d`. The theorem names are
unchanged from the former `MayerStrictPositivityAlongEx` declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d along-ex: 0 < pFE under `0 < t` and polymers exist**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_pos_of_t_pos_of_polymers_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty) :
    0 < IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t :=
  Ambient.polymerFreeEnergyAlongExhaustion_pos_of_t_pos_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_t_pos n h_poly

/-- **ℤ^d along-ex: 0 < pFE(tanh) under `0 < tanh` and polymers
exist**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J)) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty) :
    0 < IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (Real.tanh (β * J)) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_tanh_pos n h_poly

end Ambient
end IsingModel
