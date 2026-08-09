import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerTrivialCases

/-!
# ℤ^d order-zero Mayer partial sum below the free energy, along an exhaustion

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ`, the comparison placing the Mayer partial sum at truncation order `0` at or below
`polymerFreeEnergy` on the stage-`n` induced subgraph: at a bare activity under `0 ≤ t`, at
the activity `tanh (β * J)` under `0 ≤ β * J`, and in a ferromagnetic form of the latter under
`0 ≤ J` together with `0 < β`. The ferromagnetic form is the only statement here that assumes
a sign for `β` and `J` separately.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: mayerPartialSum 0 ≤ polymerFreeEnergy under
`t ≥ 0`**. -/
theorem
mayerPartialSum_zero_AlongExhaustion_latticeGraph_le_polymerFreeEnergy
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0 t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t :=
  Ambient.mayerPartialSum_zero_AlongExhaustion_le_polymerFreeEnergy
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: mayerPartialSum 0 ≤
polymerFreeEnergy(tanh(β·J))**. -/
theorem
mayerPartialSum_zero_AlongExhaustion_latticeGraph_tanh_le_polymerFreeEnergy
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) :=
  Ambient.mayerPartialSum_zero_AlongExhaustion_tanh_le_polymerFreeEnergy
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: ferromagnetic mayerPartialSum 0 ≤
polymerFreeEnergy(tanh(β·J))**. -/
theorem
mayerPartialSum_zero_AlongExhaustion_latticeGraph_tanh_le_polymerFreeEnergy_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) :=
  Ambient.mayerPartialSum_zero_AlongExhaustion_tanh_le_polymerFreeEnergy_ferromagnetic
    (IsingModel.latticeGraph d) Λ hJ hβ n

end Ambient
end IsingModel
