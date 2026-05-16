import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerTrivialCasesIdentity

/-!
# Mayer trivial-case wrappers along an exhaustion

Narrow child module for along-exhaustion `mayerPartialSum 0 ≤ polymerFreeEnergy`
comparisons and Mayer identity wrappers for no-polymer, trivial, and edgeless
cases. This keeps callers that only need these forwarders out of the
monolithic original special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 mayerPartialSum_zero ≤ polymerFreeEnergy along-ex wraps -/

/-- **Along-ex: mayerPartialSum 0 ≤ polymerFreeEnergy under `t ≥ 0`**. -/
theorem mayerPartialSum_zero_AlongExhaustion_le_polymerFreeEnergy
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) 0 t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t :=
  mayerPartialSum_zero_Λ_le_polymerFreeEnergy G (Λ.volume n) ht

/-- **Along-ex: mayerPartialSum 0 ≤ polymerFreeEnergy(tanh(β·J))**. -/
theorem mayerPartialSum_zero_AlongExhaustion_tanh_le_polymerFreeEnergy
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) :=
  mayerPartialSum_zero_Λ_tanh_le_polymerFreeEnergy G (Λ.volume n) hβJ

/-- **Along-ex: ferromagnetic mayerPartialSum 0 ≤
polymerFreeEnergy(tanh(β·J))**. -/
theorem
mayerPartialSum_zero_AlongExhaustion_tanh_le_polymerFreeEnergy_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) :=
  mayerPartialSum_zero_Λ_tanh_le_polymerFreeEnergy_ferromagnetic
    G (Λ.volume n) hJ hβ

/-! ## Moved: mayer_identity edge-case wrappers

The five `mayer_identity_of_*_AlongExhaustion` wrappers now live in
`IsingModel.AmbientLattice.SpecialCases.MayerTrivialCasesIdentity`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
