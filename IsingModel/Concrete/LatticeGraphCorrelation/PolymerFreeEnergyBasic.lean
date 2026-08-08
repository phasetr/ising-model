import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds

/-!
# ℤ^d Λ polymerFreeEnergy trivial activities and nonnegative sandwich (§18.5)

Instantiates at fixed volume `Λ` on `IsingModel.latticeGraph d` the polymer free energy at
the two trivial activities — it vanishes at `t = 0` and is the logarithm of the number of
vertex-disjoint compatible polymer families at `t = 1` — together with its two-sided bound
between `0` and `|E| * log (1 + t)` for `0 ≤ t`. These are the ℤ^d base values against which
the GJ §18.5 cluster-expansion estimates are calibrated.
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

end Ambient
end IsingModel
