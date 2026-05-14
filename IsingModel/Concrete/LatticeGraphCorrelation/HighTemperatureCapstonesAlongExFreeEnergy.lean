import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureCapstones

/-!
# Concrete along-ex freeEnergyAlongExhaustion HT capstone wrappers

Narrow child module for 3 ℤ^d along-exhaustion §18.6
freeEnergyAlongExhaustion capstone wrappers extracted from
`HighTemperatureCapstonesAlongEx.lean`:

* `freeEnergyAlongExhaustion_latticeGraph_eq_polymerFreeEnergy`,
* `freeEnergyAlongExhaustion_latticeGraph_eq_polymerFreeEnergy_ferro`,
* `freeEnergyAlongExhaustion_latticeGraph_eq_log_two_at_betaJ_zero`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.freeEnergyAlongExhaustion_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `HighTemperatureCapstonesAlongEx` declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d along-ex: §18.6 freeEnergy decomposition**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_polymerFreeEnergy
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ)
    (hne : (Λ.volume n).Nonempty) :
    Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β⟩ n =
      Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)).edgeFinset.card : ℝ) /
            Fintype.card ↑(Λ.volume n : Finset (Fin d → ℤ)) *
          Real.log (Real.cosh (β * J)) +
        IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (Real.tanh (β * J)) /
            Fintype.card ↑(Λ.volume n : Finset (Fin d → ℤ)) :=
  Ambient.freeEnergyAlongExhaustion_eq_polymerFreeEnergy
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d along-ex: §18.6 ferromagnetic freeEnergy decomposition**. -/
theorem
freeEnergyAlongExhaustion_latticeGraph_eq_polymerFreeEnergy_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β⟩ n =
      Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)).edgeFinset.card : ℝ) /
            Fintype.card ↑(Λ.volume n : Finset (Fin d → ℤ)) *
          Real.log (Real.cosh (β * J)) +
        IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (Real.tanh (β * J)) /
            Fintype.card ↑(Λ.volume n : Finset (Fin d → ℤ)) :=
  Ambient.freeEnergyAlongExhaustion_eq_polymerFreeEnergy_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n hne

/-- **ℤ^d along-ex: freeEnergy = log 2 at `β·J = 0`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_log_two_at_betaJ_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β⟩ n = Real.log 2 :=
  Ambient.freeEnergyAlongExhaustion_eq_log_two_at_betaJ_zero
    (IsingModel.latticeGraph d) Λ hβJ n hne

end Ambient
end IsingModel
