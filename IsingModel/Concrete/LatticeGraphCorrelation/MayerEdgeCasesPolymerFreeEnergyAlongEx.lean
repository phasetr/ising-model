import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerEdgeCases

/-!
# ℤ^d Mayer identity at vanishing coupling or inverse temperature

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ`, the agreement of `polymerFreeEnergy` on the stage-`n` induced subgraph with the
Mayer partial sum at every truncation order, at the activity `tanh (β * J)` with `J` replaced
by `0` and with `β` replaced by `0`. Their common specialization with both parameters replaced
by `0` is retained here; the two single-parameter statements use the canonical subject-oriented
API in `MayerEdgeCasesAlongExPolymer.lean`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: Mayer identity at `J = β = 0` (polymer_free_energy form)**. -/
theorem
mayer_identity_at_either_zero_polymer_free_energy_AlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh ((0 : ℝ) * (0 : ℝ))) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh ((0 : ℝ) * (0 : ℝ))) :=
  Ambient.mayer_identity_at_either_zero_polymer_free_energy_AlongExhaustion
    (IsingModel.latticeGraph d) Λ N n

end Ambient
end IsingModel
