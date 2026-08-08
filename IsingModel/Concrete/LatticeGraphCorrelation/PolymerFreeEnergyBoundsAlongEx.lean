import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsNonneg
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsMonotoneOn

/-!
# ℤ^d AlongExhaustion polymerFreeEnergy sign, bounds and monotonicity (§18.5)

Instantiates along an exhaustion at `IsingModel.latticeGraph d` the elementary envelope of
the polymer free energy: nonnegativity and the ceilings `|E| * log (1 + t)` and `|E| * t` for
`0 ≤ t`, together with monotonicity on `Set.Ici 0`. These are the ℤ^d bounds that keep the
GJ §18.5 cluster expansion under control stage by stage.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: polymerFreeEnergy ≥ 0 under t ≥ 0**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_nonneg_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t :=
  Ambient.polymerFreeEnergyAlongExhaustion_nonneg_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: polymerFreeEnergy ≤ |E| · log(1+t) under t ≥ 0**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_le_card_log_one_plus_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t ≤
      (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card *
        Real.log (1 + t) :=
  Ambient.polymerFreeEnergyAlongExhaustion_le_card_log_one_plus_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: polymerFreeEnergy ≤ |E| · t under t ≥ 0**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_le_card_mul_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t ≤
      (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card * t :=
  Ambient.polymerFreeEnergyAlongExhaustion_le_card_mul_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: polymerFreeEnergy MonotoneOn (Set.Ici 0)**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_monotoneOn_Ici_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    MonotoneOn (fun t : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t)
      (Set.Ici 0) :=
  Ambient.polymerFreeEnergyAlongExhaustion_monotoneOn_Ici_zero
    (IsingModel.latticeGraph d) Λ n

end Ambient
end IsingModel
