import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaEpsilonIff

/-!
# ℤ^d positivity and vanishing of the polymer free energy at the `tanh` activity

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the
characterisations of when `polymerFreeEnergy` at the activity `tanh (β * J)` is strictly
positive and of when it vanishes: strict positivity holds exactly when that activity is
strictly positive and the induced subgraph has at least one polymer, and vanishing holds
exactly when the activity is `0` or that subgraph has none. Each statement assumes `0 ≤ β * J`
and nothing else about the parameters.
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
