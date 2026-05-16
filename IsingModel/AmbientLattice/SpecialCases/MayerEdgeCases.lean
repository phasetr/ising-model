import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerEdgeCasesPFE
import IsingModel.AmbientLattice.SpecialCases.MayerEdgeCasesPolymerFreeEnergy
import IsingModel.AmbientLattice.SpecialCases.MayerEdgeCasesTrivial

/-!
# Mayer edge-case wrappers along an exhaustion

Narrow child module for along-exhaustion Mayer identity edge cases and
`polymerFreeEnergy = mayerPartialSum` wrappers. This keeps callers that only
need these forwarders out of the monolithic original special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 mayer_identity_at edge-case along-ex wraps -/

/-- **Along-ex: Mayer identity at `t = 0`**. -/
theorem mayer_identity_at_zero_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n)),
              ∏ P ∈ Γ, (0 : ℝ) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N 0 :=
  mayer_identity_at_zero_Λ G (Λ.volume n) N

/-- **Along-ex: Mayer identity at `β·J = 0`**. -/
theorem mayer_identity_at_betaJ_zero_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) (n : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n)),
              ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  mayer_identity_at_betaJ_zero_Λ G (Λ.volume n) hβJ N

/-! ## Moved: 2 trivial-slice Mayer identity wrappers

The two along-ex `mayer_identity_at_*_zero_AlongExhaustion` trivial-slice
wrappers (`_beta_zero`, `_J_zero`) now live in
`IsingModel.AmbientLattice.SpecialCases.MayerEdgeCasesTrivial`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

/-! ## Moved: polymerFreeEnergyAlongExhaustion eq mayerPartialSum wrappers

The four `polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_*`
wrappers (`zero`, `betaJ_zero`, `beta_zero`, `J_zero`) now live in
`MayerEdgeCasesPolymerFreeEnergy.lean`. They are re-imported here so
downstream consumers continue to see the symbols. -/



/-! ## Moved: mayer_identity polymer_free_energy edge-case wrappers

The three
`mayer_identity_at_*_polymer_free_energy_AlongExhaustion`
wrappers (`_J_zero`, `_beta_zero`, `_either_zero`) now live in
`IsingModel.AmbientLattice.SpecialCases.MayerEdgeCasesPFE`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
