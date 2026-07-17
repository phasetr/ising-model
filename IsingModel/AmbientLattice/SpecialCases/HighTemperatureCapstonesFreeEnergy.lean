import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaCapstones

/-!
# §18.6 freeEnergyAlongExhaustion = polymerFreeEnergy decomposition wrappers

Narrow child module for the two §18.6 ambient alongExhaustion
free-energy decomposition wrappers extracted from
`HighTemperatureCapstones.lean`:

* `freeEnergyAlongExhaustion_eq_polymerFreeEnergy`
* `freeEnergyAlongExhaustion_eq_polymerFreeEnergy_ferromagnetic`

Each wrapper is a thin pass-through to the corresponding
`freeEnergyΛ_eq_polymerFreeEnergy*` ambient lemma expressing the
free energy as `log 2 + cosh correction + polymer correction`.
Theorem names are unchanged from the former
`HighTemperatureCapstones` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: §18.6 freeEnergy decomposition** under `0 ≤ β·J` and
`(Λ.volume n).Nonempty`. -/
theorem freeEnergyAlongExhaustion_eq_polymerFreeEnergy
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ ⟨J, 0, β⟩ n =
      Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
            Fintype.card ↑(Λ.volume n : Finset V) *
          Real.log (Real.cosh (β * J)) +
        IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
          (Real.tanh (β * J)) /
            Fintype.card ↑(Λ.volume n : Finset V) :=
  freeEnergyΛ_eq_polymerFreeEnergy G (Λ.volume n) J β hβJ hne

/-- **Along-ex: §18.6 ferromagnetic freeEnergy decomposition**. -/
theorem freeEnergyAlongExhaustion_eq_polymerFreeEnergy_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ ⟨J, 0, β⟩ n =
      Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
            Fintype.card ↑(Λ.volume n : Finset V) *
          Real.log (Real.cosh (β * J)) +
        IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
          (Real.tanh (β * J)) /
            Fintype.card ↑(Λ.volume n : Finset V) :=
  freeEnergyΛ_eq_polymerFreeEnergy_ferromagnetic
    G (Λ.volume n) J β hJ hβ hne

end Ambient
end IsingModel
