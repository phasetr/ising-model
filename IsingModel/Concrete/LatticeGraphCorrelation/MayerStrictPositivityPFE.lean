import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaEpsilonIff

/-!
# ℤ^d strict positivity of the polymer free energy, on a fixed volume

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the strict
positivity of `polymerFreeEnergy` on the induced subgraph once that subgraph has at least one
polymer: at a bare activity under `0 < t`, and at the activity `tanh (β * J)` under
`0 < tanh (β * J)`. Strict positivity is assumed of whichever activity the statement uses, and
no sign condition on `β` or `J` separately is imposed.
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
