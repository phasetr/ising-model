import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds

/-!
# Concrete basic polymer free-energy wrappers

Narrow child module for concrete `ℤ^d` `polymerFreeEnergy` at-zero, at-one,
and nonnegative sandwich wrappers. This keeps callers that only need these
forwarders out of the monolithic lattice-correlation module.
-/

namespace IsingModel
namespace Ambient

/-! ### §18.5 polymerFreeEnergy at-zero/at-one + sandwich ℤ^d wraps -/

/-- **ℤ^d Λ: polymerFreeEnergy at `t = 0`** = 0. -/
theorem polymerFreeEnergy_Λ_latticeGraph_at_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) 0 = 0 :=
  Ambient.polymerFreeEnergy_Λ_at_zero (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: polymerFreeEnergy at `t = 1`** =
`log |vdCompatiblePolymerFamilies|`. -/
theorem polymerFreeEnergy_Λ_latticeGraph_at_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) 1 =
      Real.log (IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph (IsingModel.latticeGraph d) Λ)).card :=
  Ambient.polymerFreeEnergy_Λ_at_one (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: polymerFreeEnergy sandwich for `t ≥ 0`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_sandwich_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t ≤
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.log (1 + t) :=
  Ambient.polymerFreeEnergy_Λ_sandwich_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-! ## Moved: AlongExhaustion basic wrappers

The three wrappers
`polymerFreeEnergyAlongExhaustion_latticeGraph_at_zero`,
`polymerFreeEnergyAlongExhaustion_latticeGraph_at_one`,
`polymerFreeEnergyAlongExhaustion_latticeGraph_sandwich_of_nonneg` now
live in `PolymerFreeEnergyBasicAlongEx.lean`. -/


end Ambient
end IsingModel
