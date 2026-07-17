import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaCapstones

/-!
# Concrete Λ-direct freeEnergyΛ high-temperature capstone wrappers

Narrow child module for 3 ℤ^d Λ-direct §18.6 freeEnergyΛ capstone
wrappers extracted from `HighTemperatureCapstones.lean`:

* `freeEnergyΛ_latticeGraph_eq_polymerFreeEnergy`,
* `freeEnergyΛ_latticeGraph_eq_polymerFreeEnergy_ferromagnetic`,
* `freeEnergyΛ_latticeGraph_eq_log_two_at_betaJ_zero`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.freeEnergyΛ_*` lemma at `G := IsingModel.latticeGraph d`.
The theorem names are unchanged from the former
`HighTemperatureCapstones` declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d Λ: §18.6 freeEnergy decomposition**. -/
theorem freeEnergyΛ_latticeGraph_eq_polymerFreeEnergy
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : Λ.Nonempty) :
    Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ =
      Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d)
            Λ).edgeFinset.card : ℝ) /
            Fintype.card ↑(Λ : Finset (Fin d → ℤ)) *
          Real.log (Real.cosh (β * J)) +
        IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (Real.tanh (β * J)) /
            Fintype.card ↑(Λ : Finset (Fin d → ℤ)) :=
  Ambient.freeEnergyΛ_eq_polymerFreeEnergy
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d Λ: §18.6 ferromagnetic freeEnergy decomposition**. -/
theorem freeEnergyΛ_latticeGraph_eq_polymerFreeEnergy_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : Λ.Nonempty) :
    Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ =
      Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d)
            Λ).edgeFinset.card : ℝ) /
            Fintype.card ↑(Λ : Finset (Fin d → ℤ)) *
          Real.log (Real.cosh (β * J)) +
        IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (Real.tanh (β * J)) /
            Fintype.card ↑(Λ : Finset (Fin d → ℤ)) :=
  Ambient.freeEnergyΛ_eq_polymerFreeEnergy_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ hne

/-- **ℤ^d Λ: freeEnergy = log 2 at `β·J = 0`**. -/
theorem freeEnergyΛ_latticeGraph_eq_log_two_at_betaJ_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (hne : Λ.Nonempty) :
    Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ =
      Real.log 2 :=
  Ambient.freeEnergyΛ_eq_log_two_at_betaJ_zero
    (IsingModel.latticeGraph d) Λ hβJ hne

end Ambient
end IsingModel
