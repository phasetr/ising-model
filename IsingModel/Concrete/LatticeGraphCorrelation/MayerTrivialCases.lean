import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerIdentity

/-!
# ℤ^d order-zero Mayer partial sum below the polymer free energy

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the comparison
placing the Mayer partial sum at truncation order `0` at or below `polymerFreeEnergy` on the
induced subgraph: at a bare activity under `0 ≤ t`, at the activity `tanh (β * J)` under
`0 ≤ β * J`, and in a ferromagnetic form of the latter under `0 ≤ J` together with `0 < β`.
The ferromagnetic form is the only statement here that assumes a sign for `β` and `J`
separately.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **ℤ^d Λ: mayerPartialSum 0 ≤ polymerFreeEnergy under `t ≥ 0`**. -/
theorem mayerPartialSum_zero_Λ_latticeGraph_le_polymerFreeEnergy
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 0 t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t :=
  Ambient.mayerPartialSum_zero_Λ_le_polymerFreeEnergy
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: mayerPartialSum 0 ≤ polymerFreeEnergy(tanh(β·J))**. -/
theorem mayerPartialSum_zero_Λ_latticeGraph_tanh_le_polymerFreeEnergy
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) :=
  Ambient.mayerPartialSum_zero_Λ_tanh_le_polymerFreeEnergy
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: ferromagnetic mayerPartialSum 0 ≤
polymerFreeEnergy(tanh(β·J))**. -/
theorem
mayerPartialSum_zero_Λ_latticeGraph_tanh_le_polymerFreeEnergy_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) :=
  Ambient.mayerPartialSum_zero_Λ_tanh_le_polymerFreeEnergy_ferromagnetic
    (IsingModel.latticeGraph d) Λ hJ hβ

end Ambient
end IsingModel
