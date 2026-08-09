import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerStrictPositivity

/-!
# ℤ^d strict positivity of the polymer free energy, along an exhaustion

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ`, the strict positivity of `polymerFreeEnergy` on the stage-`n` induced subgraph
once that subgraph has at least one polymer: at a bare activity under `0 < t`, and at the
activity `tanh (β * J)` under `0 < tanh (β * J)`. Strict positivity is assumed of whichever
activity the statement uses, and no sign condition on `β` or `J` separately is imposed.
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
