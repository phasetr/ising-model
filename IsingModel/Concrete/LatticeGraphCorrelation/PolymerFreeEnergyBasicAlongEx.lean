import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBasic

/-!
# ℤ^d AlongExhaustion polymerFreeEnergy trivial activities and sandwich (§18.5)

Instantiates along an exhaustion at `IsingModel.latticeGraph d` the polymer free energy at
the two trivial activities — it vanishes at `t = 0` and is the logarithm of the number of
vertex-disjoint compatible polymer families at `t = 1` — together with its two-sided bound
between `0` and `|E| * log (1 + t)` for `0 ≤ t`. These are the ℤ^d base values against which
the GJ §18.5 cluster-expansion estimates are calibrated, stage by stage.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: polymerFreeEnergy at `t = 0`** = 0. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_at_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0 = 0 :=
  Ambient.polymerFreeEnergyAlongExhaustion_at_zero
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: polymerFreeEnergy at `t = 1`**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_at_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 1 =
      Real.log (IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))).card :=
  Ambient.polymerFreeEnergyAlongExhaustion_at_one
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: polymerFreeEnergy sandwich for `t ≥ 0`**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_sandwich_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t ≤
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n)).edgeFinset.card * Real.log (1 + t) :=
  Ambient.polymerFreeEnergyAlongExhaustion_sandwich_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

end Ambient
end IsingModel
