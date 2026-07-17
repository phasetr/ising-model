import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsNonneg
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsMonotoneOn

/-!
# ℤ^d along-exhaustion polymerFreeEnergy bound wrappers

Narrow child module for four ℤ^d
`polymerFreeEnergyAlongExhaustion_latticeGraph_*` bound wrappers
extracted from `PolymerFreeEnergyBounds.lean`:

* `polymerFreeEnergyAlongExhaustion_latticeGraph_nonneg_of_nonneg`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_le_card_log_one_plus_of_nonneg`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_le_card_mul_of_nonneg`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_monotoneOn_Ici_zero`.

Each result is a thin pass-through of the ambient
`Ambient.polymerFreeEnergyAlongExhaustion_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `PolymerFreeEnergyBounds` declarations.
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
