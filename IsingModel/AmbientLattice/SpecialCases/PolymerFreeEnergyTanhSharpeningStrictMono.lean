import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening

/-!
# Polymer free-energy tanh `StrictMonoOn` wrappers along an exhaustion

Narrow child module for the two §18.5 along-exhaustion
`polymerFreeEnergyAlongExhaustion_tanh_strictMonoOn_*` wrappers
extracted from `PolymerFreeEnergyTanhSharpening.lean`:

* `polymerFreeEnergyAlongExhaustion_tanh_strictMonoOn_beta_of_polymers_nonempty`
* `polymerFreeEnergyAlongExhaustion_tanh_strictMonoOn_J_of_polymers_nonempty`

Each wrapper is a thin pass-through to the corresponding ambient
`polymerFreeEnergy_Λ_tanh_strictMonoOn_*_of_polymers_nonempty`
lemma stating that `pFE(tanh(β·J))` is `StrictMonoOn (Set.Ici 0)`
in `β` (resp. `J`) under nonempty polymer family. Theorem names are
unchanged from the former `PolymerFreeEnergyTanhSharpening`
declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: pFE(tanh(β·J)) is `StrictMonoOn (Set.Ici 0)` in β**
under `J > 0` and polymers nonempty. -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_strictMonoOn_beta_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty)
    {J : ℝ} (hJ : 0 < J) :
    StrictMonoOn (fun β : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)))
      (Set.Ici 0) :=
  polymerFreeEnergy_Λ_tanh_strictMonoOn_beta_of_polymers_nonempty
    G (Λ.volume n) h_poly hJ

/-- **Along-ex: pFE(tanh(β·J)) is `StrictMonoOn (Set.Ici 0)` in J**
under `β > 0` and polymers nonempty. -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_strictMonoOn_J_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty)
    {β : ℝ} (hβ : 0 < β) :
    StrictMonoOn (fun J : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)))
      (Set.Ici 0) :=
  polymerFreeEnergy_Λ_tanh_strictMonoOn_J_of_polymers_nonempty
    G (Λ.volume n) h_poly hβ

end Ambient
end IsingModel
